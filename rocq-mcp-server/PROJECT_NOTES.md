# MCP Coq/Rocq Server - Project Notes and Objectives

## What We Are Building

We are creating an MCP (Model Context Protocol) server that enables Large Language Models (LLMs) to interact with the Coq/Rocq theorem proving system. This server acts as a bridge between AI systems and formal verification tools, allowing LLMs to:

1. Write and verify mathematical proofs
2. Perform formal verification of software
3. Engage in certified programming
4. Access the entire Coq ecosystem through OPAM

## Primary Goal

The main objective is to provide LLMs with comprehensive access to theorem proving capabilities through a standardized protocol (MCP), enabling them to:
- Assist humans in developing formal proofs
- Verify correctness of algorithms and data structures
- Generate certified code through extraction
- Learn from and contribute to formal mathematics

## Architecture Overview

```
LLM (Claude/GPT/etc.) <--> MCP Protocol <--> Our Server <--> Coq/Rocq Process
                                                    |
                                                    v
                                            OPAM Libraries Ecosystem
```

## What Was Achieved

### ✅ Core Functionality
- Full MCP server implementation with 40+ specialized tools
- Coq process management with session handling
- Command execution, proof state tracking, tactic application
- File operations (load, save, compile)
- OPAM package management integration

### ✅ Library Support
Successfully integrated support for major Coq libraries:
- Mathematical Components (MathComp)
- Automation tools (CoqHammer, QuickChick)
- Verification frameworks (Iris, CompCert)
- Mathematical libraries (Flocq, Coquelicot, CoRN)
- Advanced features (MetaCoq, HoTT, UniMath)

### ✅ Deployment
- Docker container with pre-installed libraries
- Build system and project structure
- Example files and test infrastructure

## What Still Needs Work

### 🔴 Critical Security Issues

1. **Command Injection Vulnerabilities**
   - The `CoqManager.executeCommand()` method directly passes user input to shell processes
   - No sanitization of file paths in `loadFile()`, `saveFile()`, `compile()`
   - OPAM commands (`opamInstall`, `opamSearch`) execute with user-provided strings
   - Need input validation and command sanitization

2. **Process Isolation**
   - Coq processes run with full system permissions
   - No sandboxing or containerization at the process level
   - Should implement process isolation using Docker containers or VMs per session

3. **Resource Limits**
   - No memory limits on Coq processes
   - No CPU time limits (only basic timeouts)
   - No disk space quotas for file operations
   - Risk of DoS through resource exhaustion

4. **File System Access**
   - Unrestricted file system access through paths
   - No chroot jail or restricted directories
   - Should implement path traversal prevention and whitelisted directories

### 🟡 Error Handling Improvements Needed

1. **Process Management**
   ```typescript
   // Current issue: Process crashes not handled gracefully
   // Need: Process health monitoring and automatic restart
   // Need: Zombie process cleanup
   ```

2. **Timeout Handling**
   ```typescript
   // Current: Fixed 30-second timeout
   // Need: Configurable timeouts per operation type
   // Need: Graceful timeout with partial results
   ```

3. **Error Recovery**
   - No session recovery after crashes
   - No checkpointing of proof state
   - No transaction-like rollback for failed operations

4. **Error Messages**
   - Generic error messages don't provide actionable information
   - Stack traces exposed to clients (information leak)
   - Need structured error codes and safe error messages

### 🟡 Exception Handling Gaps

1. **Async/Promise Rejection**
   - Unhandled promise rejections in several places
   - Missing try-catch blocks in async handlers
   - Need global uncaught exception handlers

2. **Stream Handling**
   - stdout/stderr streams not properly managed
   - Buffer overflow possible with large outputs
   - Need stream backpressure handling

3. **Child Process Issues**
   - SIGTERM/SIGKILL not handled properly
   - Orphaned processes possible
   - Need proper process cleanup on server shutdown

## Security Improvements Required

### Input Validation Layer
```typescript
class InputValidator {
  static validateCoqCommand(command: string): string {
    // Remove shell metacharacters
    // Validate Coq syntax
    // Check command whitelist
    return sanitizedCommand;
  }
  
  static validateFilePath(path: string): string {
    // Prevent path traversal
    // Enforce allowed directories
    // Validate file extensions
    return safePath;
  }
}
```

### Session Isolation
```typescript
class IsolatedSession {
  private container: DockerContainer;
  private resourceLimits: ResourceLimits;
  
  async execute(command: string): Promise<string> {
    // Execute in isolated container
    // Monitor resource usage
    // Kill if limits exceeded
  }
}
```

### Rate Limiting
```typescript
class RateLimiter {
  private requestCounts: Map<string, number>;
  private windowStart: Date;
  
  canExecute(sessionId: string, operation: string): boolean {
    // Check request rate
    // Implement exponential backoff
    // Block abusive sessions
  }
}
```

## Additional Features Needed

1. **Authentication & Authorization**
   - No user authentication currently
   - No access control for operations
   - Need API key or token-based auth

2. **Audit Logging**
   - No audit trail of operations
   - Need structured logging for security events
   - Should track: who, what, when, result

3. **Monitoring & Metrics**
   - No performance metrics collection
   - No health checks beyond basic Docker HEALTHCHECK
   - Need Prometheus/OpenTelemetry integration

4. **State Persistence**
   - Sessions lost on server restart
   - No way to save/restore proof state
   - Need Redis or database for session storage

## Coq-Specific Security Considerations

While Coq itself is relatively safe (proofs can't perform I/O without explicit extraction), we need to handle:

1. **Extraction Safety**
   - Extracted code (OCaml/Haskell) can perform arbitrary operations
   - Need to sandbox extraction output
   - Should scan extracted code for dangerous patterns

2. **Plugin Security**
   - Some Coq plugins can execute arbitrary code
   - Need plugin whitelist/blacklist
   - Should audit plugin usage

3. **Resource Bombs**
   - Infinite loops in tactics
   - Exponential proof search
   - Memory exhaustion through large terms

## Recommended Implementation Priority

1. **Immediate (Security Critical)**
   - Input sanitization for all user inputs
   - Process isolation using containers
   - Resource limits (memory, CPU, disk)

2. **Short Term (Stability)**
   - Comprehensive error handling
   - Process health monitoring
   - Graceful degradation

3. **Medium Term (Production Ready)**
   - Authentication system
   - Audit logging
   - Monitoring and metrics
   - State persistence

4. **Long Term (Enterprise)**
   - Multi-tenancy support
   - Distributed session management
   - Load balancing
   - High availability

## Testing Requirements

Currently missing:
- Unit tests for input validation
- Integration tests for process management
- Security penetration testing
- Load/stress testing
- Fuzzing for command parser

## Conclusion

While the core functionality is implemented and the server can perform theorem proving operations, it is **NOT production-ready** due to critical security vulnerabilities and insufficient error handling. The current implementation should be considered a **proof of concept** that demonstrates the integration between MCP and Coq but requires significant hardening before deployment in any environment where security matters.

The server in its current state is suitable for:
- Local development and experimentation
- Controlled research environments
- Educational purposes

It should NOT be used for:
- Public-facing services
- Multi-user environments
- Processing untrusted input
- Production systems

## Next Steps

1. Implement input validation layer
2. Add process isolation
3. Improve error handling
4. Add comprehensive logging
5. Write security tests
6. Document security model
7. Perform security audit