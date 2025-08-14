import { spawn } from 'child_process';
import { v4 as uuidv4 } from 'uuid';
import * as fs from 'fs/promises';
import * as path from 'path';
import { createLogger } from './logger.js';
const logger = createLogger();
export class CoqManager {
    sessions = new Map();
    activeSessionId = null;
    async initSession(libraries, workspace) {
        const sessionId = uuidv4();
        const workDir = workspace || process.cwd();
        const coqProcess = spawn('coqtop', ['-q'], {
            cwd: workDir,
            env: { ...process.env },
            stdio: ['pipe', 'pipe', 'pipe'],
        });
        const session = {
            id: sessionId,
            process: coqProcess,
            history: [],
            workspace: workDir,
            currentGoals: '',
            proofDepth: 0,
        };
        this.sessions.set(sessionId, session);
        this.activeSessionId = sessionId;
        // Wait for coqtop to be ready by waiting for initial prompt
        await new Promise((resolve) => {
            const handler = (data) => {
                const text = data.toString();
                if (text.includes('Coq <')) {
                    session.process.stderr?.removeListener('data', handler);
                    resolve(undefined);
                }
            };
            session.process.stderr?.on('data', handler);
            // Timeout after 2 seconds
            setTimeout(() => {
                session.process.stderr?.removeListener('data', handler);
                resolve(undefined);
            }, 2000);
        });
        // Load requested libraries
        if (libraries && libraries.length > 0) {
            for (const lib of libraries) {
                try {
                    await this.requireLibrary(lib, true, false);
                }
                catch (e) {
                    logger.warn(`Failed to load library ${lib}: ${e}`);
                }
            }
        }
        logger.info(`Initialized Coq session ${sessionId}`);
        return `Session initialized with ID: ${sessionId}\nWorkspace: ${workDir}`;
    }
    async executeCommand(command, sessionId) {
        const session = this.getSession(sessionId);
        if (!session) {
            throw new Error('No active Coq session. Initialize one with coq_init first.');
        }
        return new Promise((resolve, reject) => {
            let output = '';
            let errorOutput = '';
            let buffer = '';
            const timeout = setTimeout(() => {
                reject(new Error('Command execution timeout'));
            }, 30000);
            const dataHandler = (data) => {
                const text = data.toString();
                output += text;
            };
            const errorHandler = (data) => {
                const text = data.toString();
                errorOutput += text;
                // Check if we've received the prompt (which comes on stderr)
                if (text.includes('Coq <') || text.includes('< ')) {
                    clearTimeout(timeout);
                    // Remove event listeners
                    session.process.stdout?.removeListener('data', dataHandler);
                    session.process.stderr?.removeListener('data', errorHandler);
                    // Clean up the output
                    const result = output.trim();
                    session.history.push(command);
                    // Check for errors in the output
                    if (result.includes('Error:')) {
                        resolve(result);
                    }
                    else {
                        resolve(result || 'Command executed successfully');
                    }
                }
            };
            session.process.stdout?.on('data', dataHandler);
            session.process.stderr?.on('data', errorHandler);
            // Send the command
            session.process.stdin?.write(command + '\n');
        });
    }
    async checkType(term) {
        return this.executeCommand(`Check ${term}.`);
    }
    async getGoals(detailed) {
        const session = this.getSession();
        if (!session) {
            return 'No active session';
        }
        if (session.proofDepth === 0) {
            return 'No proof in progress';
        }
        const command = detailed ? 'Show.' : 'Show.';
        return this.executeCommand(command);
    }
    async search(pattern, type) {
        let searchCommand = 'Search';
        if (type && type !== 'all') {
            searchCommand = `Search${type.charAt(0).toUpperCase() + type.slice(1)}`;
        }
        return this.executeCommand(`${searchCommand} "${pattern}".`);
    }
    async print(name, options) {
        let printCommand = 'Print';
        if (options && options.length > 0) {
            printCommand = `Print ${options.join(' ')}`;
        }
        return this.executeCommand(`${printCommand} ${name}.`);
    }
    async undo(steps = 1) {
        const session = this.getSession();
        if (!session) {
            throw new Error('No active session');
        }
        if (session.proofDepth > 0) {
            return this.executeCommand(`Undo ${steps}.`);
        }
        else {
            return this.executeCommand(`Back ${steps}.`);
        }
    }
    async reset(point) {
        if (point) {
            return this.executeCommand(`Reset ${point}.`);
        }
        else {
            return this.executeCommand('Reset Initial.');
        }
    }
    async loadFile(filePath, compile) {
        try {
            if (compile) {
                await this.compile(filePath);
            }
            const content = await fs.readFile(filePath, 'utf-8');
            const lines = content.split('\n');
            let results = [];
            for (const line of lines) {
                if (line.trim() && !line.trim().startsWith('(*')) {
                    const result = await this.executeCommand(line);
                    results.push(result);
                }
            }
            return `File ${filePath} loaded successfully.\n${results.join('\n')}`;
        }
        catch (error) {
            throw new Error(`Failed to load file: ${error}`);
        }
    }
    async saveFile(filePath, content) {
        try {
            const session = this.getSession();
            if (!session) {
                throw new Error('No active session');
            }
            const finalContent = content || session.history.join('\n');
            await fs.writeFile(filePath, finalContent);
            return `File saved to ${filePath}`;
        }
        catch (error) {
            throw new Error(`Failed to save file: ${error}`);
        }
    }
    async compile(filePath, options) {
        return new Promise((resolve, reject) => {
            const args = [filePath, ...(options || [])];
            const coqc = spawn('coqc', args);
            let output = '';
            let errorOutput = '';
            coqc.stdout.on('data', (data) => {
                output += data.toString();
            });
            coqc.stderr.on('data', (data) => {
                errorOutput += data.toString();
            });
            coqc.on('close', (code) => {
                if (code === 0) {
                    resolve(`Compilation successful: ${filePath}`);
                }
                else {
                    reject(new Error(`Compilation failed: ${errorOutput}`));
                }
            });
        });
    }
    async requireLibrary(library, doImport = true, doExport = false) {
        let command = 'Require';
        if (doExport) {
            command += ' Export';
        }
        else if (doImport) {
            command += ' Import';
        }
        command += ` ${library}.`;
        return this.executeCommand(command);
    }
    async applyTactic(tactic, all = false) {
        const session = this.getSession();
        if (!session) {
            throw new Error('No active session');
        }
        if (session.proofDepth === 0) {
            throw new Error('No proof in progress');
        }
        const tacticCommand = all ? `all: ${tactic}.` : `${tactic}.`;
        return this.executeCommand(tacticCommand);
    }
    async admit() {
        return this.executeCommand('Admitted.');
    }
    async abort() {
        return this.executeCommand('Abort.');
    }
    async getInfo() {
        // Get version without requiring a session
        return new Promise((resolve, reject) => {
            const coqProcess = spawn('coqc', ['--version']);
            let output = '';
            coqProcess.stdout?.on('data', (data) => {
                output += data.toString();
            });
            coqProcess.on('close', (code) => {
                if (code === 0) {
                    resolve(output);
                }
                else {
                    resolve('Coq is installed but version information is unavailable');
                }
            });
            coqProcess.on('error', (err) => {
                resolve('Coq is not installed or not in PATH');
            });
            // Add timeout manually
            setTimeout(() => {
                coqProcess.kill();
                resolve('Coq version check timed out');
            }, 5000);
        });
    }
    async extract(target, definitions, output) {
        let extractCommands = [];
        // Set extraction language
        switch (target) {
            case 'ocaml':
                extractCommands.push('Extraction Language OCaml.');
                break;
            case 'haskell':
                extractCommands.push('Extraction Language Haskell.');
                break;
            case 'scheme':
                extractCommands.push('Extraction Language Scheme.');
                break;
        }
        // Extract definitions
        if (output) {
            extractCommands.push(`Extraction "${output}" ${definitions.join(' ')}.`);
        }
        else {
            extractCommands.push(`Extraction ${definitions.join(' ')}.`);
        }
        let results = [];
        for (const cmd of extractCommands) {
            results.push(await this.executeCommand(cmd));
        }
        return results.join('\n');
    }
    async opamList(filter) {
        return new Promise((resolve, reject) => {
            const args = ['list', '--installed'];
            if (filter) {
                args.push(filter);
            }
            const opam = spawn('opam', args);
            let output = '';
            opam.stdout.on('data', (data) => {
                output += data.toString();
            });
            opam.on('close', (code) => {
                if (code === 0) {
                    // Filter for Coq packages
                    const lines = output.split('\n');
                    const coqPackages = lines.filter(line => line.includes('coq-'));
                    resolve(coqPackages.join('\n'));
                }
                else {
                    reject(new Error('Failed to list OPAM packages'));
                }
            });
        });
    }
    async opamInstall(packageName, version) {
        return new Promise((resolve, reject) => {
            const packageSpec = version ? `${packageName}.${version}` : packageName;
            const opam = spawn('opam', ['install', '-y', packageSpec]);
            let output = '';
            let errorOutput = '';
            opam.stdout.on('data', (data) => {
                output += data.toString();
            });
            opam.stderr.on('data', (data) => {
                errorOutput += data.toString();
            });
            opam.on('close', (code) => {
                if (code === 0) {
                    resolve(`Successfully installed ${packageSpec}`);
                }
                else {
                    reject(new Error(`Failed to install package: ${errorOutput}`));
                }
            });
        });
    }
    async opamSearch(query) {
        return new Promise((resolve, reject) => {
            const opam = spawn('opam', ['search', query]);
            let output = '';
            opam.stdout.on('data', (data) => {
                output += data.toString();
            });
            opam.on('close', (code) => {
                if (code === 0) {
                    // Filter for Coq packages
                    const lines = output.split('\n');
                    const coqPackages = lines.filter(line => line.includes('coq-'));
                    resolve(coqPackages.join('\n'));
                }
                else {
                    reject(new Error('Failed to search OPAM packages'));
                }
            });
        });
    }
    async projectInit(name, projectPath, libraries) {
        try {
            // Create project directory
            await fs.mkdir(projectPath, { recursive: true });
            // Create _CoqProject file
            let coqProjectContent = `-Q . ${name}\n`;
            if (libraries && libraries.length > 0) {
                for (const lib of libraries) {
                    coqProjectContent += `-arg -w -arg -notation-overridden\n`;
                }
            }
            await fs.writeFile(path.join(projectPath, '_CoqProject'), coqProjectContent);
            // Create Makefile
            const makefileContent = `COQMAKEFILE := Makefile.coq
COQMAKE := \$(COQBIN)coq_makefile

all: \$(COQMAKEFILE)
\t\$(MAKE) -f \$(COQMAKEFILE)

\$(COQMAKEFILE): _CoqProject
\t\$(COQMAKE) -f _CoqProject -o \$(COQMAKEFILE)

clean:
\tif [ -e \$(COQMAKEFILE) ]; then \$(MAKE) -f \$(COQMAKEFILE) clean; fi
\trm -f \$(COQMAKEFILE) \$(COQMAKEFILE).conf

.PHONY: all clean
`;
            await fs.writeFile(path.join(projectPath, 'Makefile'), makefileContent);
            // Create src directory
            await fs.mkdir(path.join(projectPath, 'src'), { recursive: true });
            // Create theories directory
            await fs.mkdir(path.join(projectPath, 'theories'), { recursive: true });
            return `Project ${name} initialized at ${projectPath}`;
        }
        catch (error) {
            throw new Error(`Failed to initialize project: ${error}`);
        }
    }
    async projectBuild(projectPath, system = 'make') {
        return new Promise((resolve, reject) => {
            const buildCommand = system === 'dune' ? 'dune' : 'make';
            const buildArgs = system === 'dune' ? ['build'] : [];
            const build = spawn(buildCommand, buildArgs, { cwd: projectPath });
            let output = '';
            let errorOutput = '';
            build.stdout.on('data', (data) => {
                output += data.toString();
            });
            build.stderr.on('data', (data) => {
                errorOutput += data.toString();
            });
            build.on('close', (code) => {
                if (code === 0) {
                    resolve(`Build successful:\n${output}`);
                }
                else {
                    reject(new Error(`Build failed:\n${errorOutput}`));
                }
            });
        });
    }
    async executeLtac2(code) {
        return this.executeCommand(`From Ltac2 Require Import Ltac2.\n${code}`);
    }
    async executeEquations(definition) {
        const setupCommands = [
            'From Equations Require Import Equations.',
            definition
        ];
        let results = [];
        for (const cmd of setupCommands) {
            results.push(await this.executeCommand(cmd));
        }
        return results.join('\n');
    }
    async executeMathComp(command, module) {
        let setupCommands = [];
        if (module) {
            setupCommands.push(`From mathcomp Require Import ${module}.`);
        }
        setupCommands.push(command);
        let results = [];
        for (const cmd of setupCommands) {
            results.push(await this.executeCommand(cmd));
        }
        return results.join('\n');
    }
    async executeHammer(mode, timeout) {
        const setupCommands = [
            'From Hammer Require Import Hammer.',
            'Set Hammer ATPLimit ' + (timeout || 10) + '.'
        ];
        let results = [];
        for (const cmd of setupCommands) {
            results.push(await this.executeCommand(cmd));
        }
        const hammerCommand = mode || 'hammer';
        results.push(await this.executeCommand(`${hammerCommand}.`));
        return results.join('\n');
    }
    async executeQuickChick(property, samples) {
        const setupCommands = [
            'From QuickChick Require Import QuickChick.',
            `QuickChick ${property}.`
        ];
        let results = [];
        for (const cmd of setupCommands) {
            results.push(await this.executeCommand(cmd));
        }
        return results.join('\n');
    }
    async executeFiatCrypto(operation, parameters) {
        const setupCommands = [
            'Require Import Crypto.Arithmetic.',
            'Require Import Crypto.PushButtonSynthesis.',
            operation
        ];
        let results = [];
        for (const cmd of setupCommands) {
            results.push(await this.executeCommand(cmd));
        }
        return results.join('\n');
    }
    async executeCompCert(command) {
        const setupCommands = [
            'Require Import compcert.common.AST.',
            'Require Import compcert.common.Values.',
            command
        ];
        let results = [];
        for (const cmd of setupCommands) {
            results.push(await this.executeCommand(cmd));
        }
        return results.join('\n');
    }
    async executeIris(logic, heap) {
        const setupCommands = [
            'From iris Require Import iris.',
            heap ? `From iris.heap_lang Require Import ${heap}.` : '',
            logic
        ].filter(cmd => cmd);
        let results = [];
        for (const cmd of setupCommands) {
            results.push(await this.executeCommand(cmd));
        }
        return results.join('\n');
    }
    async executeMetaCoq(command, term) {
        const setupCommands = [
            'From MetaCoq Require Import All.',
            command
        ];
        if (term) {
            setupCommands.push(`Quote Definition quoted := ${term}.`);
            setupCommands.push('Print quoted.');
        }
        let results = [];
        for (const cmd of setupCommands) {
            results.push(await this.executeCommand(cmd));
        }
        return results.join('\n');
    }
    async executeUniMath(module, command) {
        const setupCommands = module
            ? [`Require Import UniMath.${module}.`, command]
            : ['Require Import UniMath.Foundations.All.', command];
        let results = [];
        for (const cmd of setupCommands) {
            results.push(await this.executeCommand(cmd));
        }
        return results.join('\n');
    }
    async executeHoTT(command) {
        const setupCommands = [
            'Require Import HoTT.',
            command
        ];
        let results = [];
        for (const cmd of setupCommands) {
            results.push(await this.executeCommand(cmd));
        }
        return results.join('\n');
    }
    async executeCoqEAL(operation) {
        const setupCommands = [
            'From CoqEAL Require Import hrel param refinements.',
            operation
        ];
        let results = [];
        for (const cmd of setupCommands) {
            results.push(await this.executeCommand(cmd));
        }
        return results.join('\n');
    }
    async executeFlocq(command) {
        const setupCommands = [
            'Require Import Flocq.Core.Core.',
            command
        ];
        let results = [];
        for (const cmd of setupCommands) {
            results.push(await this.executeCommand(cmd));
        }
        return results.join('\n');
    }
    async executeCoquelicot(command) {
        const setupCommands = [
            'Require Import Coquelicot.Coquelicot.',
            command
        ];
        let results = [];
        for (const cmd of setupCommands) {
            results.push(await this.executeCommand(cmd));
        }
        return results.join('\n');
    }
    async executeCoRN(command) {
        const setupCommands = [
            'Require Import CoRN.algebra.RSetoid.',
            'Require Import CoRN.metric2.Metric.',
            command
        ];
        let results = [];
        for (const cmd of setupCommands) {
            results.push(await this.executeCommand(cmd));
        }
        return results.join('\n');
    }
    getSession(sessionId) {
        const id = sessionId || this.activeSessionId;
        if (!id) {
            logger.warn('No session ID provided and no active session');
            return undefined;
        }
        const session = this.sessions.get(id);
        if (!session) {
            logger.warn(`Session ${id} not found`);
            if (id === this.activeSessionId) {
                this.activeSessionId = null;
            }
        }
        return session;
    }
    async closeSession(sessionId) {
        const session = this.getSession(sessionId);
        if (session) {
            try {
                session.process.stdin?.end();
                session.process.kill('SIGTERM');
                // Give it time to close gracefully
                setTimeout(() => {
                    if (!session.process.killed) {
                        session.process.kill('SIGKILL');
                    }
                }, 1000);
            }
            catch (error) {
                logger.error(`Error closing session ${session.id}:`, error);
            }
            this.sessions.delete(session.id);
            if (this.activeSessionId === session.id) {
                this.activeSessionId = null;
            }
            logger.info(`Closed session ${session.id}`);
        }
    }
    async closeAllSessions() {
        const sessionIds = Array.from(this.sessions.keys());
        await Promise.all(sessionIds.map(id => this.closeSession(id)));
        logger.info('All sessions closed');
    }
    getSessionInfo() {
        return {
            active: this.activeSessionId,
            total: this.sessions.size,
            ids: Array.from(this.sessions.keys()),
        };
    }
}
//# sourceMappingURL=coq-manager.js.map