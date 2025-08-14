# MCP Coq/Rocq Server

A comprehensive Model Context Protocol (MCP) server for Coq/Rocq theorem proving, providing LLMs with powerful tools to engage in formal verification, theorem proving, and mathematical reasoning.

## Features

### Core Theorem Proving
- **Session Management**: Initialize and manage multiple Coq sessions
- **Command Execution**: Execute arbitrary Coq commands
- **Proof State**: Track goals, apply tactics, manage proof progress
- **Type Checking**: Check types of terms and expressions
- **Search & Discovery**: Search for theorems, definitions, and lemmas

### Advanced Capabilities
- **Library Management**: Full OPAM integration for package management
- **Project Management**: Initialize and build Coq projects
- **File Operations**: Load, save, and compile Coq files
- **Code Extraction**: Extract verified code to OCaml, Haskell, or Scheme

### Supported Libraries

The server provides specialized support for major Coq libraries:

- **Mathematical Components (MathComp)**: SSReflect and algebraic structures
- **CoqHammer**: Automated theorem proving with ATP integration
- **QuickChick**: Property-based testing
- **Fiat-Crypto**: Cryptographic code generation
- **CompCert**: Verified C compiler
- **Iris**: Separation logic framework
- **MetaCoq**: Metacircular Coq framework
- **UniMath**: Univalent mathematics
- **HoTT**: Homotopy Type Theory
- **CoqEAL**: Effective Algebra Library
- **Flocq**: Floating-point arithmetic
- **Coquelicot**: Real analysis
- **CoRN**: Constructive real numbers
- **Ltac2**: Modern tactic language
- **Equations**: Advanced pattern matching

## Installation

### Prerequisites

1. Install Coq/Rocq:
```bash
# Using OPAM
opam init
opam switch create coq-switch 4.14.1
eval $(opam env)
opam install coq
```

2. Install Node.js (v18 or higher)

### Setup

1. Clone the repository:
```bash
git clone <repository-url>
cd mcp-coq-server
```

2. Install dependencies:
```bash
npm install
```

3. Build the server:
```bash
npm run build
```

4. Install Coq libraries (optional but recommended):
```bash
# Mathematical Components
opam install coq-mathcomp-ssreflect coq-mathcomp-algebra

# Automation tools
opam install coq-hammer coq-quickchick

# Verification frameworks
opam install coq-iris coq-compcert

# Mathematics libraries
opam install coq-coquelicot coq-flocq coq-corn

# Advanced features
opam install coq-equations coq-metacoq
```

## Usage

### Starting the Server

```bash
npm start
```

Or in development mode:
```bash
npm run dev
```

### MCP Client Configuration

Add to your MCP client configuration:

```json
{
  "mcpServers": {
    "coq": {
      "command": "node",
      "args": ["/path/to/mcp-coq-server/dist/index.js"],
      "env": {
        "LOG_LEVEL": "info"
      }
    }
  }
}
```

## Available Tools

### Basic Operations

#### coq_init
Initialize a new Coq session.
```json
{
  "libraries": ["Arith", "List", "mathcomp.ssreflect"],
  "workspace": "/path/to/project"
}
```

#### coq_exec
Execute a Coq command.
```json
{
  "command": "Definition nat_id (n : nat) : nat := n."
}
```

#### coq_check
Check the type of a term.
```json
{
  "term": "nat_id"
}
```

### Proof Management

#### coq_goals
Display current proof goals.
```json
{
  "detailed": true
}
```

#### coq_tactic
Apply a tactic to the current goal.
```json
{
  "tactic": "intros",
  "all": false
}
```

#### coq_search
Search for theorems and definitions.
```json
{
  "pattern": "plus_comm",
  "type": "theorem"
}
```

### Library Management

#### coq_opam_search
Search for Coq packages.
```json
{
  "query": "algebra"
}
```

#### coq_opam_install
Install a Coq package.
```json
{
  "package": "coq-mathcomp-field",
  "version": "1.15.0"
}
```

### Project Management

#### coq_project_init
Initialize a new Coq project.
```json
{
  "name": "MyProject",
  "path": "/path/to/project",
  "libraries": ["mathcomp", "stdpp"]
}
```

#### coq_project_build
Build a Coq project.
```json
{
  "path": "/path/to/project",
  "system": "make"
}
```

### Advanced Features

#### coq_hammer
Use CoqHammer for automated proving.
```json
{
  "mode": "hammer",
  "timeout": 30
}
```

#### coq_quickchick
Property-based testing.
```json
{
  "property": "prop_reverse_involutive",
  "samples": 1000
}
```

#### coq_extract
Extract verified code.
```json
{
  "target": "ocaml",
  "definitions": ["mergesort", "binary_search"],
  "output": "extracted.ml"
}
```

## Examples

### Example 1: Simple Proof

```javascript
// Initialize session
await coq_init({ libraries: ["Arith"] });

// Define a theorem
await coq_exec({ 
  command: "Theorem plus_comm : forall n m : nat, n + m = m + n." 
});

// Start proof
await coq_exec({ command: "Proof." });

// Apply tactics
await coq_tactic({ tactic: "intros n m" });
await coq_tactic({ tactic: "induction n" });
await coq_tactic({ tactic: "simpl" });
await coq_tactic({ tactic: "reflexivity" });
await coq_tactic({ tactic: "simpl" });
await coq_tactic({ tactic: "rewrite IHn" });
await coq_tactic({ tactic: "simpl" });
await coq_tactic({ tactic: "reflexivity" });

// Complete proof
await coq_exec({ command: "Qed." });
```

### Example 2: Using MathComp

```javascript
// Initialize with MathComp
await coq_init({ 
  libraries: ["mathcomp.ssreflect.ssreflect"] 
});

// Use SSReflect tactics
await coq_mathcomp({ 
  command: "Lemma example : 2 + 2 = 4.",
  module: "ssreflect"
});

await coq_exec({ command: "Proof. by []. Qed." });
```

### Example 3: Property-Based Testing

```javascript
// Load QuickChick
await coq_require({ 
  library: "QuickChick.QuickChick" 
});

// Define a property
await coq_exec({ 
  command: "Definition prop_reverse (l : list nat) := reverse (reverse l) = l." 
});

// Test the property
await coq_quickchick({ 
  property: "prop_reverse",
  samples: 1000
});
```

### Example 4: Verified Extraction

```javascript
// Define a verified sorting function
await coq_exec({ 
  command: `
    Fixpoint insert (x : nat) (l : list nat) : list nat :=
      match l with
      | nil => x :: nil
      | h :: t => if x <=? h then x :: l else h :: insert x t
      end.
    
    Fixpoint insertion_sort (l : list nat) : list nat :=
      match l with
      | nil => nil
      | h :: t => insert h (insertion_sort t)
      end.
  `
});

// Extract to OCaml
await coq_extract({ 
  target: "ocaml",
  definitions: ["insertion_sort"],
  output: "sort.ml"
});
```

## Docker Support

A Dockerfile is provided for easy deployment with pre-installed libraries.

### Building the Docker Image

```bash
docker build -t mcp-coq-server .
```

### Running the Container

```bash
docker run -it mcp-coq-server
```

## Architecture

The server is built with:
- **TypeScript**: Type-safe implementation
- **MCP SDK**: Standard protocol implementation
- **Child Process Management**: Robust Coq process handling
- **Session Management**: Multiple concurrent Coq sessions
- **Logging**: Comprehensive logging with Winston

## Troubleshooting

### Common Issues

1. **Coq not found**: Ensure Coq is installed and in PATH
2. **OPAM packages missing**: Run `opam install <package-name>`
3. **Session timeout**: Increase timeout in coq-manager.ts
4. **Memory issues**: Adjust Node.js memory limit with `--max-old-space-size`

### Debug Mode

Enable debug logging:
```bash
LOG_LEVEL=debug npm start
```

## Contributing

Contributions are welcome! Please ensure:
1. Code follows TypeScript best practices
2. All tools are properly documented
3. Tests are included for new features

## License

MIT

## Support

For issues and questions:
- GitHub Issues: [repository-issues]
- Documentation: [documentation-url]

## Roadmap

- [ ] SerAPI integration for better proof state management
- [ ] LSP support for IDE integration
- [ ] Proof script replay and debugging
- [ ] Proof search and mining capabilities
- [ ] Integration with proof assistants databases
- [ ] Support for Coq plugins development
- [ ] Proof visualization tools
- [ ] Automated proof repair
- [ ] Integration with CI/CD pipelines
- [ ] Support for proof certificates