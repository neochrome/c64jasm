
import { readFileSync } from 'fs';
import { EventEmitter } from 'events';

import { ChildProcess } from 'child_process'
import * as child_process from 'child_process'
import * as net from 'net';

export interface C64jasmBreakpoint {
    id: number;
    line: number;
    verified: boolean;
}

class MonitorConnection {
    private client: net.Socket;

    constructor() {
    }

    connect() {
        this.client = net.createConnection({ port: 6510, timeout:5000 }, () => {
            console.log('Connected to VICE monitor');
            this.client.write('disass\r\n');
        })

        this.client.on('data', function(data) {
            console.log('Received: ' + data);
        });
    }
}

// Talk to a running c64jasm process that's watching a source file for changes.
// It will report current output binary and debug information.
class C64JasmDebugInfo {
    private client: net.Socket;

    c64jasm: {
        outputPrg: string;
        debugInfo: {
            pcToLocs: {
                [pc: string]: {
                    lineNo: number, source: string
                }[];
            }
        }
    } = undefined;

    constructor() {
    }

    connect() {
        const port = 6502;

        this.client = net.createConnection({ port, timeout:5000 }, () => {
            console.log('Connected to c64jasm');
            this.client.write('debug-info\r\n');
        })

        const self = this;
        const chunks: Buffer[] = [];
        this.client.on('data', data => {
            chunks.push(data);
        }).on('end', () => {
            self.c64jasm = JSON.parse(Buffer.concat(chunks).toString());
        });
    }

    // This is a super expensive function but at least for now,
    // it's only ever run when setting a breakpoint from the UI.
    findSourceLoc (path: string, line: number): number|undefined {
        if (this.c64jasm) {
            const pclocs = this.c64jasm.debugInfo.pcToLocs;
            for (const pc of Object.keys(pclocs)) {
                const locList = pclocs[pc];
                for (let i = 0; i < locList.length; i++) {
                    const loc = locList[i];
                    if (loc.source == path && loc.lineNo == line) {
                        return parseInt(pc, 10);
                    }
                }
            }
        }
        return null;
    }
}

function sleep(ms: number) {
  return new Promise(resolve => setTimeout(resolve, ms));
}

/**
 * A C64jasm runtime with minimal debugger functionality.
 */
export class C64jasmRuntime extends EventEmitter {

    // the initial (and one and only) file we are 'debugging'
    private _sourceFile: string;
    public get sourceFile() {
        return this._sourceFile;
    }

    // the contents (= lines) of the one and only file
    private _sourceLines: string[];

    // This is the next line that will be 'executed'
    private _currentLine = 0;

    // maps from sourceFile to array of C64jasm breakpoints
    private _breakPoints = new Map<string, C64jasmBreakpoint[]>();

    // since we want to send breakpoint events, we will assign an id to every event
    // so that the frontend can match events with breakpoints.
    private _breakpointId = 1;

    private _viceProcess: ChildProcess = null;
    private _monitor: MonitorConnection;
    private _debugInfo: C64JasmDebugInfo = new C64JasmDebugInfo();

    constructor() {
        super();
    }

    /**
     * Start executing the given program.
     */
    public async start(program: string, stopOnEntry: boolean) {
        // Ask c64jasm compiler for debug information.  This is done
        // by connecting to a running c64jasm process that's watching
        // source files for changes.
        this._debugInfo.connect();

        this._viceProcess = child_process.exec(`x64 -remotemonitor ${program}`);
        await sleep(5000);

        this._monitor = new MonitorConnection();
        this._monitor.connect();

        // Stop the debugger once the VICE process exits.
        this._viceProcess.on('close', (code, signal) => {
            this.sendEvent('end');
        })
        this._currentLine = -1;

        this.verifyBreakpoints(this._sourceFile);

        if (stopOnEntry) {
            // we step once
            this.step(false, 'stopOnEntry');
        } else {
            // we just start to run until we hit a breakpoint or an exception
            this.continue();
        }
    }

    public terminate() {
        this._viceProcess.kill();
    }

    /**
     * Continue execution to the end/beginning.
     */
    public continue(reverse = false) {
        this.run(reverse, undefined);
    }

    /**
     * Step to the next/previous non empty line.
     */
    public step(reverse = false, event = 'stopOnStep') {
        this.run(reverse, event);
    }

    /**
     * Returns a fake 'stacktrace' where every 'stackframe' is a word from the current line.
     */
    public stack(startFrame: number, endFrame: number): any {

        const words = this._sourceLines[this._currentLine].trim().split(/\s+/);

        const frames = new Array<any>();
        // every word of the current line becomes a stack frame.
        for (let i = startFrame; i < Math.min(endFrame, words.length); i++) {
            const name = words[i];	// use a word of the line as the stackframe name
            frames.push({
                index: i,
                name: `${name}(${i})`,
                file: this._sourceFile,
                line: this._currentLine
            });
        }
        return {
            frames: frames,
            count: words.length
        };
    }

    /*
     * Set breakpoint in file with given line.
     */
    public setBreakPoint(path: string, line: number) : C64jasmBreakpoint {
        const dbg = this._debugInfo.findSourceLoc(path, line);
        console.log({dbg});
        const bp = <C64jasmBreakpoint> { verified: false, line, id: this._breakpointId++ };
        let bps = this._breakPoints.get(path);
        if (!bps) {
            bps = new Array<C64jasmBreakpoint>();
            this._breakPoints.set(path, bps);
        }
        bps.push(bp);

        this.verifyBreakpoints(path);

        return bp;
    }

    /*
     * Clear breakpoint in file with given line.
     */
    public clearBreakPoint(path: string, line: number) : C64jasmBreakpoint | undefined {
        let bps = this._breakPoints.get(path);
        if (bps) {
            const index = bps.findIndex(bp => bp.line === line);
            if (index >= 0) {
                const bp = bps[index];
                bps.splice(index, 1);
                return bp;
            }
        }
        return undefined;
    }

    /*
     * Clear all breakpoints for file.
     */
    public clearBreakpoints(path: string): void {
        this._breakPoints.delete(path);
    }

    // private methods

    private loadSource(file: string) {
        if (this._sourceFile !== file) {
            this._sourceFile = file;
            this._sourceLines = readFileSync(this._sourceFile).toString().split('\n');
        }
    }

    /**
     * Run through the file.
     * If stepEvent is specified only run a single step and emit the stepEvent.
     */
    private run(reverse = false, stepEvent?: string) {
        return;
/*        for (let ln = this._currentLine+1; ln < this._sourceLines.length; ln++) {
            if (this.fireEventsForLine(ln, stepEvent)) {
                this._currentLine = ln;
                return;
            }
        }
        // no more lines: run to end
        this.sendEvent('end');*/
    }

    private verifyBreakpoints(path: string) : void {
        let bps = this._breakPoints.get(path);
        if (bps) {
            this.loadSource(path);
            bps.forEach(bp => {
                if (!bp.verified && bp.line < this._sourceLines.length) {
                    const srcLine = this._sourceLines[bp.line].trim();

                    // if a line is empty or starts with '+' we don't allow to set a breakpoint but move the breakpoint down
                    if (srcLine.length === 0 || srcLine.indexOf('+') === 0) {
                        bp.line++;
                    }
                    // if a line starts with '-' we don't allow to set a breakpoint but move the breakpoint up
                    if (srcLine.indexOf('-') === 0) {
                        bp.line--;
                    }
                    // don't set 'verified' to true if the line contains the word 'lazy'
                    // in this case the breakpoint will be verified 'lazy' after hitting it once.
                    if (srcLine.indexOf('lazy') < 0) {
                        bp.verified = true;
                        this.sendEvent('breakpointValidated', bp);
                    }
                }
            });
        }
    }

    /**
     * Fire events if line has a breakpoint or the word 'exception' is found.
     * Returns true is execution needs to stop.
     */
    private fireEventsForLine(ln: number, stepEvent?: string): boolean {

        const line = this._sourceLines[ln].trim();

        // if 'log(...)' found in source -> send argument to debug console
        const matches = /log\((.*)\)/.exec(line);
        if (matches && matches.length === 2) {
            this.sendEvent('output', matches[1], this._sourceFile, ln, matches.index)
        }

        // if word 'exception' found in source -> throw exception
        if (line.indexOf('exception') >= 0) {
            this.sendEvent('stopOnException');
            return true;
        }

        // is there a breakpoint?
        const breakpoints = this._breakPoints.get(this._sourceFile);
        if (breakpoints) {
            const bps = breakpoints.filter(bp => bp.line === ln);
            if (bps.length > 0) {

                // send 'stopped' event
                this.sendEvent('stopOnBreakpoint');

                // the following shows the use of 'breakpoint' events to update properties of a breakpoint in the UI
                // if breakpoint is not yet verified, verify it now and send a 'breakpoint' update event
                if (!bps[0].verified) {
                    bps[0].verified = true;
                    this.sendEvent('breakpointValidated', bps[0]);
                }
                return true;
            }
        }

        // non-empty line
        if (stepEvent && line.length > 0) {
            this.sendEvent(stepEvent);
            return true;
        }

        // nothing interesting found -> continue
        return false;
    }

    private sendEvent(event: string, ... args: any[]) {
        setImmediate(_ => {
            this.emit(event, ...args);
        });
    }
}