#!/usr/bin/env node
import { Server } from '@modelcontextprotocol/sdk/server/index.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import { CallToolRequestSchema, ListToolsRequestSchema, } from '@modelcontextprotocol/sdk/types.js';
import { CoqManager } from './coq-manager.js';
import { createLogger } from './logger.js';
import { validateNumber } from './validators.js';
const logger = createLogger();
class CoqMCPServer {
    server;
    coqManager;
    constructor() {
        this.server = new Server({
            name: 'mcp-coq-server',
            version: '1.0.0',
        }, {
            capabilities: {
                tools: {},
            },
        });
        this.coqManager = new CoqManager();
        this.setupHandlers();
    }
    setupHandlers() {
        this.server.setRequestHandler(ListToolsRequestSchema, async () => {
            logger.info('ListTools request received');
            return {
                tools: this.getTools(),
            };
        });
        this.server.setRequestHandler(CallToolRequestSchema, async (request) => {
            const { name, arguments: args } = request.params;
            logger.info(`Tool called: ${name}`, { args });
            try {
                switch (name) {
                    case 'coq_init':
                        return await this.handleCoqInit(args);
                    case 'coq_exec':
                        return await this.handleCoqExec(args);
                    case 'coq_check':
                        return await this.handleCoqCheck(args);
                    case 'coq_goals':
                        return await this.handleCoqGoals(args);
                    case 'coq_search':
                        return await this.handleCoqSearch(args);
                    case 'coq_print':
                        return await this.handleCoqPrint(args);
                    case 'coq_undo':
                        return await this.handleCoqUndo(args);
                    case 'coq_reset':
                        return await this.handleCoqReset(args);
                    case 'coq_load_file':
                        return await this.handleCoqLoadFile(args);
                    case 'coq_save_file':
                        return await this.handleCoqSaveFile(args);
                    case 'coq_compile':
                        return await this.handleCoqCompile(args);
                    case 'coq_require':
                        return await this.handleCoqRequire(args);
                    case 'coq_tactic':
                        return await this.handleCoqTactic(args);
                    case 'coq_admit':
                        return await this.handleCoqAdmit(args);
                    case 'coq_abort':
                        return await this.handleCoqAbort(args);
                    case 'coq_info':
                        return await this.handleCoqInfo(args);
                    case 'coq_extract':
                        return await this.handleCoqExtract(args);
                    case 'coq_opam_list':
                        return await this.handleOpamList(args);
                    case 'coq_opam_install':
                        return await this.handleOpamInstall(args);
                    case 'coq_opam_search':
                        return await this.handleOpamSearch(args);
                    case 'coq_project_init':
                        return await this.handleProjectInit(args);
                    case 'coq_project_build':
                        return await this.handleProjectBuild(args);
                    case 'coq_ltac2':
                        return await this.handleLtac2(args);
                    case 'coq_equations':
                        return await this.handleEquations(args);
                    case 'coq_mathcomp':
                        return await this.handleMathComp(args);
                    case 'coq_hammer':
                        return await this.handleHammer(args);
                    case 'coq_quickchick':
                        return await this.handleQuickChick(args);
                    case 'coq_fiat_crypto':
                        return await this.handleFiatCrypto(args);
                    case 'coq_compcert':
                        return await this.handleCompCert(args);
                    case 'coq_iris':
                        return await this.handleIris(args);
                    case 'coq_metacoq':
                        return await this.handleMetaCoq(args);
                    case 'coq_unimath':
                        return await this.handleUniMath(args);
                    case 'coq_hott':
                        return await this.handleHoTT(args);
                    case 'coq_coqeal':
                        return await this.handleCoqEAL(args);
                    case 'coq_flocq':
                        return await this.handleFlocq(args);
                    case 'coq_coquelicot':
                        return await this.handleCoquelicot(args);
                    case 'coq_corn':
                        return await this.handleCoRN(args);
                    default:
                        throw new Error(`Unknown tool: ${name}`);
                }
            }
            catch (error) {
                logger.error(`Error executing tool ${name}:`, error);
                return {
                    content: [
                        {
                            type: 'text',
                            text: `Error: ${error instanceof Error ? error.message : String(error)}`,
                        },
                    ],
                };
            }
        });
    }
    getTools() {
        return [
            {
                name: 'coq_init',
                description: 'Initialize a new Coq session with optional libraries',
                inputSchema: {
                    type: 'object',
                    properties: {
                        libraries: {
                            type: 'array',
                            items: { type: 'string' },
                            description: 'List of libraries to load (e.g., ["Arith", "List", "mathcomp.ssreflect"])',
                        },
                        workspace: {
                            type: 'string',
                            description: 'Working directory for the Coq session',
                        },
                    },
                },
            },
            {
                name: 'coq_exec',
                description: 'Execute a Coq command or sentence',
                inputSchema: {
                    type: 'object',
                    properties: {
                        command: {
                            type: 'string',
                            description: 'The Coq command to execute',
                        },
                        sessionId: {
                            type: 'string',
                            description: 'Optional session ID for multi-session support',
                        },
                    },
                    required: ['command'],
                },
            },
            {
                name: 'coq_check',
                description: 'Check the type of a Coq term',
                inputSchema: {
                    type: 'object',
                    properties: {
                        term: {
                            type: 'string',
                            description: 'The term to check',
                        },
                    },
                    required: ['term'],
                },
            },
            {
                name: 'coq_goals',
                description: 'Display current proof goals',
                inputSchema: {
                    type: 'object',
                    properties: {
                        detailed: {
                            type: 'boolean',
                            description: 'Show detailed goal information',
                        },
                    },
                },
            },
            {
                name: 'coq_search',
                description: 'Search for theorems, definitions, or patterns',
                inputSchema: {
                    type: 'object',
                    properties: {
                        pattern: {
                            type: 'string',
                            description: 'Search pattern (supports wildcards)',
                        },
                        type: {
                            type: 'string',
                            enum: ['theorem', 'definition', 'lemma', 'all'],
                            description: 'Type of objects to search for',
                        },
                    },
                    required: ['pattern'],
                },
            },
            {
                name: 'coq_print',
                description: 'Print a definition, theorem, or module',
                inputSchema: {
                    type: 'object',
                    properties: {
                        name: {
                            type: 'string',
                            description: 'Name of the object to print',
                        },
                        options: {
                            type: 'array',
                            items: { type: 'string' },
                            description: 'Print options (e.g., ["All", "Implicit"])',
                        },
                    },
                    required: ['name'],
                },
            },
            {
                name: 'coq_undo',
                description: 'Undo the last n commands',
                inputSchema: {
                    type: 'object',
                    properties: {
                        steps: {
                            type: 'number',
                            description: 'Number of steps to undo (default: 1)',
                            default: 1,
                        },
                    },
                },
            },
            {
                name: 'coq_reset',
                description: 'Reset to a named point or clear the session',
                inputSchema: {
                    type: 'object',
                    properties: {
                        point: {
                            type: 'string',
                            description: 'Named point to reset to (optional)',
                        },
                    },
                },
            },
            {
                name: 'coq_load_file',
                description: 'Load a Coq file (.v)',
                inputSchema: {
                    type: 'object',
                    properties: {
                        path: {
                            type: 'string',
                            description: 'Path to the Coq file',
                        },
                        compile: {
                            type: 'boolean',
                            description: 'Compile the file first',
                            default: false,
                        },
                    },
                    required: ['path'],
                },
            },
            {
                name: 'coq_save_file',
                description: 'Save current proof script to a file',
                inputSchema: {
                    type: 'object',
                    properties: {
                        path: {
                            type: 'string',
                            description: 'Path where to save the file',
                        },
                        content: {
                            type: 'string',
                            description: 'Content to save (optional, uses session history if not provided)',
                        },
                    },
                    required: ['path'],
                },
            },
            {
                name: 'coq_compile',
                description: 'Compile a Coq file to .vo',
                inputSchema: {
                    type: 'object',
                    properties: {
                        path: {
                            type: 'string',
                            description: 'Path to the Coq file',
                        },
                        options: {
                            type: 'array',
                            items: { type: 'string' },
                            description: 'Compilation options',
                        },
                    },
                    required: ['path'],
                },
            },
            {
                name: 'coq_require',
                description: 'Require a Coq library or module',
                inputSchema: {
                    type: 'object',
                    properties: {
                        library: {
                            type: 'string',
                            description: 'Library name (e.g., "Coq.Arith.Arith")',
                        },
                        import: {
                            type: 'boolean',
                            description: 'Import the library namespace',
                            default: true,
                        },
                        export: {
                            type: 'boolean',
                            description: 'Export the library namespace',
                            default: false,
                        },
                    },
                    required: ['library'],
                },
            },
            {
                name: 'coq_tactic',
                description: 'Apply a tactic to the current goal',
                inputSchema: {
                    type: 'object',
                    properties: {
                        tactic: {
                            type: 'string',
                            description: 'The tactic to apply',
                        },
                        all: {
                            type: 'boolean',
                            description: 'Apply to all goals',
                            default: false,
                        },
                    },
                    required: ['tactic'],
                },
            },
            {
                name: 'coq_admit',
                description: 'Admit the current goal (mark as admitted)',
                inputSchema: {
                    type: 'object',
                    properties: {},
                },
            },
            {
                name: 'coq_abort',
                description: 'Abort the current proof',
                inputSchema: {
                    type: 'object',
                    properties: {},
                },
            },
            {
                name: 'coq_info',
                description: 'Get information about Coq version and loaded modules',
                inputSchema: {
                    type: 'object',
                    properties: {},
                },
            },
            {
                name: 'coq_extract',
                description: 'Extract Coq code to OCaml, Haskell, or Scheme',
                inputSchema: {
                    type: 'object',
                    properties: {
                        target: {
                            type: 'string',
                            enum: ['ocaml', 'haskell', 'scheme'],
                            description: 'Target language',
                        },
                        definitions: {
                            type: 'array',
                            items: { type: 'string' },
                            description: 'Definitions to extract',
                        },
                        output: {
                            type: 'string',
                            description: 'Output file path',
                        },
                    },
                    required: ['target', 'definitions'],
                },
            },
            {
                name: 'coq_opam_list',
                description: 'List installed Coq packages via OPAM',
                inputSchema: {
                    type: 'object',
                    properties: {
                        filter: {
                            type: 'string',
                            description: 'Filter packages by name pattern',
                        },
                    },
                },
            },
            {
                name: 'coq_opam_install',
                description: 'Install a Coq package via OPAM',
                inputSchema: {
                    type: 'object',
                    properties: {
                        package: {
                            type: 'string',
                            description: 'Package name (e.g., "coq-mathcomp-ssreflect")',
                        },
                        version: {
                            type: 'string',
                            description: 'Specific version (optional)',
                        },
                    },
                    required: ['package'],
                },
            },
            {
                name: 'coq_opam_search',
                description: 'Search for Coq packages in OPAM',
                inputSchema: {
                    type: 'object',
                    properties: {
                        query: {
                            type: 'string',
                            description: 'Search query',
                        },
                    },
                    required: ['query'],
                },
            },
            {
                name: 'coq_project_init',
                description: 'Initialize a new Coq project with _CoqProject file',
                inputSchema: {
                    type: 'object',
                    properties: {
                        name: {
                            type: 'string',
                            description: 'Project name',
                        },
                        path: {
                            type: 'string',
                            description: 'Project directory path',
                        },
                        libraries: {
                            type: 'array',
                            items: { type: 'string' },
                            description: 'Dependencies to include',
                        },
                    },
                    required: ['name', 'path'],
                },
            },
            {
                name: 'coq_project_build',
                description: 'Build a Coq project using make or dune',
                inputSchema: {
                    type: 'object',
                    properties: {
                        path: {
                            type: 'string',
                            description: 'Project directory path',
                        },
                        system: {
                            type: 'string',
                            enum: ['make', 'dune'],
                            description: 'Build system to use',
                            default: 'make',
                        },
                    },
                    required: ['path'],
                },
            },
            {
                name: 'coq_ltac2',
                description: 'Execute Ltac2 tactics (modern tactic language)',
                inputSchema: {
                    type: 'object',
                    properties: {
                        code: {
                            type: 'string',
                            description: 'Ltac2 code to execute',
                        },
                    },
                    required: ['code'],
                },
            },
            {
                name: 'coq_equations',
                description: 'Use Equations plugin for function definitions with dependent pattern matching',
                inputSchema: {
                    type: 'object',
                    properties: {
                        definition: {
                            type: 'string',
                            description: 'Equations definition',
                        },
                    },
                    required: ['definition'],
                },
            },
            {
                name: 'coq_mathcomp',
                description: 'Access Mathematical Components library features',
                inputSchema: {
                    type: 'object',
                    properties: {
                        command: {
                            type: 'string',
                            description: 'MathComp specific command',
                        },
                        module: {
                            type: 'string',
                            description: 'MathComp module (e.g., ssreflect, algebra, fingroup)',
                        },
                    },
                    required: ['command'],
                },
            },
            {
                name: 'coq_hammer',
                description: 'Use CoqHammer for automated theorem proving',
                inputSchema: {
                    type: 'object',
                    properties: {
                        mode: {
                            type: 'string',
                            enum: ['hammer', 'sauto', 'hauto', 'qauto', 'lauto'],
                            description: 'Hammer mode to use',
                        },
                        timeout: {
                            type: 'number',
                            description: 'Timeout in seconds',
                            default: 10,
                        },
                    },
                },
            },
            {
                name: 'coq_quickchick',
                description: 'Property-based testing with QuickChick',
                inputSchema: {
                    type: 'object',
                    properties: {
                        property: {
                            type: 'string',
                            description: 'Property to test',
                        },
                        samples: {
                            type: 'number',
                            description: 'Number of test samples',
                            default: 100,
                        },
                    },
                    required: ['property'],
                },
            },
            {
                name: 'coq_fiat_crypto',
                description: 'Use Fiat-Crypto for cryptographic code generation',
                inputSchema: {
                    type: 'object',
                    properties: {
                        operation: {
                            type: 'string',
                            description: 'Cryptographic operation',
                        },
                        parameters: {
                            type: 'object',
                            description: 'Operation parameters',
                        },
                    },
                    required: ['operation'],
                },
            },
            {
                name: 'coq_compcert',
                description: 'Access CompCert verified C compiler features',
                inputSchema: {
                    type: 'object',
                    properties: {
                        command: {
                            type: 'string',
                            description: 'CompCert command',
                        },
                    },
                    required: ['command'],
                },
            },
            {
                name: 'coq_iris',
                description: 'Use Iris separation logic framework',
                inputSchema: {
                    type: 'object',
                    properties: {
                        logic: {
                            type: 'string',
                            description: 'Iris logic command',
                        },
                        heap: {
                            type: 'string',
                            description: 'Heap model to use',
                        },
                    },
                    required: ['logic'],
                },
            },
            {
                name: 'coq_metacoq',
                description: 'MetaCoq metacircular framework for Coq',
                inputSchema: {
                    type: 'object',
                    properties: {
                        command: {
                            type: 'string',
                            description: 'MetaCoq command',
                        },
                        term: {
                            type: 'string',
                            description: 'Term to process',
                        },
                    },
                    required: ['command'],
                },
            },
            {
                name: 'coq_unimath',
                description: 'UniMath univalent mathematics library',
                inputSchema: {
                    type: 'object',
                    properties: {
                        module: {
                            type: 'string',
                            description: 'UniMath module',
                        },
                        command: {
                            type: 'string',
                            description: 'Command to execute',
                        },
                    },
                    required: ['command'],
                },
            },
            {
                name: 'coq_hott',
                description: 'Homotopy Type Theory library',
                inputSchema: {
                    type: 'object',
                    properties: {
                        command: {
                            type: 'string',
                            description: 'HoTT command',
                        },
                    },
                    required: ['command'],
                },
            },
            {
                name: 'coq_coqeal',
                description: 'CoqEAL - Effective Algebra Library',
                inputSchema: {
                    type: 'object',
                    properties: {
                        operation: {
                            type: 'string',
                            description: 'Algebraic operation',
                        },
                    },
                    required: ['operation'],
                },
            },
            {
                name: 'coq_flocq',
                description: 'Flocq floating-point library',
                inputSchema: {
                    type: 'object',
                    properties: {
                        command: {
                            type: 'string',
                            description: 'Flocq command',
                        },
                    },
                    required: ['command'],
                },
            },
            {
                name: 'coq_coquelicot',
                description: 'Coquelicot real analysis library',
                inputSchema: {
                    type: 'object',
                    properties: {
                        command: {
                            type: 'string',
                            description: 'Coquelicot command',
                        },
                    },
                    required: ['command'],
                },
            },
            {
                name: 'coq_corn',
                description: 'CoRN constructive real numbers',
                inputSchema: {
                    type: 'object',
                    properties: {
                        command: {
                            type: 'string',
                            description: 'CoRN command',
                        },
                    },
                    required: ['command'],
                },
            },
        ];
    }
    async handleCoqInit(args) {
        const result = await this.coqManager.initSession(args.libraries, args.workspace);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleCoqExec(args) {
        const result = await this.coqManager.executeCommand(args.command, args.sessionId);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleCoqCheck(args) {
        const result = await this.coqManager.checkType(args.term);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleCoqGoals(args) {
        const result = await this.coqManager.getGoals(args.detailed);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleCoqSearch(args) {
        const result = await this.coqManager.search(args.pattern, args.type);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleCoqPrint(args) {
        const result = await this.coqManager.print(args.name, args.options);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleCoqUndo(args) {
        const steps = validateNumber(args.steps, 'steps', false, 1, 100) || 1;
        const result = await this.coqManager.undo(steps);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleCoqReset(args) {
        const result = await this.coqManager.reset(args.point);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleCoqLoadFile(args) {
        const result = await this.coqManager.loadFile(args.path, args.compile);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleCoqSaveFile(args) {
        const result = await this.coqManager.saveFile(args.path, args.content);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleCoqCompile(args) {
        const result = await this.coqManager.compile(args.path, args.options);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleCoqRequire(args) {
        const result = await this.coqManager.requireLibrary(args.library, args.import, args.export);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleCoqTactic(args) {
        const result = await this.coqManager.applyTactic(args.tactic, args.all);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleCoqAdmit(args) {
        const result = await this.coqManager.admit();
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleCoqAbort(args) {
        const result = await this.coqManager.abort();
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleCoqInfo(args) {
        logger.info('Getting Coq info...');
        const result = await this.coqManager.getInfo();
        logger.info('Got Coq info:', { result: result.substring(0, 50) });
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleCoqExtract(args) {
        const result = await this.coqManager.extract(args.target, args.definitions, args.output);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleOpamList(args) {
        const result = await this.coqManager.opamList(args.filter);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleOpamInstall(args) {
        const result = await this.coqManager.opamInstall(args.package, args.version);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleOpamSearch(args) {
        const result = await this.coqManager.opamSearch(args.query);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleProjectInit(args) {
        const result = await this.coqManager.projectInit(args.name, args.path, args.libraries);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleProjectBuild(args) {
        const result = await this.coqManager.projectBuild(args.path, args.system);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleLtac2(args) {
        const result = await this.coqManager.executeLtac2(args.code);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleEquations(args) {
        const result = await this.coqManager.executeEquations(args.definition);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleMathComp(args) {
        const result = await this.coqManager.executeMathComp(args.command, args.module);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleHammer(args) {
        const result = await this.coqManager.executeHammer(args.mode, args.timeout);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleQuickChick(args) {
        const result = await this.coqManager.executeQuickChick(args.property, args.samples);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleFiatCrypto(args) {
        const result = await this.coqManager.executeFiatCrypto(args.operation, args.parameters);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleCompCert(args) {
        const result = await this.coqManager.executeCompCert(args.command);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleIris(args) {
        const result = await this.coqManager.executeIris(args.logic, args.heap);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleMetaCoq(args) {
        const result = await this.coqManager.executeMetaCoq(args.command, args.term);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleUniMath(args) {
        const result = await this.coqManager.executeUniMath(args.module, args.command);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleHoTT(args) {
        const result = await this.coqManager.executeHoTT(args.command);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleCoqEAL(args) {
        const result = await this.coqManager.executeCoqEAL(args.operation);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleFlocq(args) {
        const result = await this.coqManager.executeFlocq(args.command);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleCoquelicot(args) {
        const result = await this.coqManager.executeCoquelicot(args.command);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async handleCoRN(args) {
        const result = await this.coqManager.executeCoRN(args.command);
        return {
            content: [
                {
                    type: 'text',
                    text: result,
                },
            ],
        };
    }
    async start() {
        const transport = new StdioServerTransport();
        await this.server.connect(transport);
        logger.info('Coq MCP Server started');
    }
}
const server = new CoqMCPServer();
server.start().catch((error) => {
    logger.error('Failed to start server:', error);
    process.exit(1);
});
//# sourceMappingURL=index.js.map