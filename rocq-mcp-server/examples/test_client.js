#!/usr/bin/env node

/**
 * Test client for MCP Coq Server
 * This demonstrates how to interact with the server
 */

import { Client } from '@modelcontextprotocol/sdk/client/index.js';
import { StdioClientTransport } from '@modelcontextprotocol/sdk/client/stdio.js';
import path from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

async function testCoqServer() {
  console.log('🚀 Starting MCP Coq Server test client...\n');
  console.log('=' .repeat(50) + '\n');

  let transport;
  let client;
  let testsPassed = 0;
  let testsFailed = 0;

  try {
    // Create client transport (this starts the server)
    const serverPath = path.join(__dirname, '..', 'dist', 'index.js');
    transport = new StdioClientTransport({
      command: 'node',
      args: [serverPath],
    });

    // Create client with error handling
    client = new Client({
      name: 'coq-test-client',
      version: '1.0.0',
    }, {
      capabilities: {}
    });

    // Set up error handlers
    client.onerror = (error) => {
      console.error('❌ Client error:', error);
    };

    // Connect to server with timeout
    const connectPromise = client.connect(transport);
    const timeoutPromise = new Promise((_, reject) => 
      setTimeout(() => reject(new Error('Connection timeout')), 5000)
    );
    
    await Promise.race([connectPromise, timeoutPromise]);
    console.log('✅ Connected to MCP Coq Server\n');

    // Helper function for safe tool calls
    async function safeCallTool(name, args = {}, testName = '') {
      try {
        const result = await client.callTool(name, args);
        if (result && result.content && result.content[0]) {
          console.log(`✅ ${testName || name}: Success`);
          if (result.content[0].text) {
            const preview = result.content[0].text.substring(0, 100);
            console.log(`   Result: ${preview}${result.content[0].text.length > 100 ? '...' : ''}`);
          }
          testsPassed++;
          return result;
        } else {
          throw new Error('Invalid response format');
        }
      } catch (error) {
        console.log(`❌ ${testName || name}: Failed`);
        console.log(`   Error: ${error.message}`);
        testsFailed++;
        return null;
      }
    }

    // Test 1: Initialize session
    console.log('\nTest 1: Initializing Coq session...');
    const initResult = await safeCallTool('coq_init', {
      libraries: ['Arith'],
    }, 'Initialize session');

    // Test 2: Execute a simple command
    console.log('\nTest 2: Defining a simple function...');
    if (initResult) {
      await safeCallTool('coq_exec', {
        command: 'Definition double (n : nat) : nat := n + n.',
      }, 'Define double function');
    }

    // Test 3: Check type
    console.log('\nTest 3: Checking type of double...');
    await safeCallTool('coq_check', {
      term: 'double',
    }, 'Check type');

    // Test 4: Start a proof
    console.log('\nTest 4: Starting a proof...');
    const theoremResult = await safeCallTool('coq_exec', {
      command: 'Theorem double_plus : forall n, double n = n + n.',
    }, 'Start theorem');

    if (theoremResult) {
      await safeCallTool('coq_exec', {
        command: 'Proof.',
      }, 'Begin proof');
    }

    // Test 5: Check goals
    console.log('\nTest 5: Checking current goals...');
    await safeCallTool('coq_goals', {
      detailed: true,
    }, 'Check goals');

    // Test 6: Apply tactics
    console.log('\nTest 6: Applying tactics...');
    const tactic1 = await safeCallTool('coq_tactic', {
      tactic: 'intros n',
    }, 'Apply intros');

    if (tactic1) {
      await safeCallTool('coq_tactic', {
        tactic: 'unfold double',
      }, 'Apply unfold');

      await safeCallTool('coq_tactic', {
        tactic: 'reflexivity',
      }, 'Apply reflexivity');

      await safeCallTool('coq_exec', {
        command: 'Qed.',
      }, 'Complete proof');
    }

    // Test 7: Search for theorems
    console.log('\nTest 7: Searching for plus theorems...');
    await safeCallTool('coq_search', {
      pattern: 'plus',
      type: 'theorem',
    }, 'Search theorems');

    // Test 8: Print definition
    console.log('\nTest 8: Printing nat definition...');
    await safeCallTool('coq_print', {
      name: 'nat',
    }, 'Print nat');

    // Test 9: Get Coq info
    console.log('\nTest 9: Getting Coq information...');
    await safeCallTool('coq_info', {}, 'Get Coq info');

    // Test 10: List available tools
    console.log('\nTest 10: Listing available tools...');
    try {
      const toolsResponse = await client.listTools();
      console.log(`✅ Found ${toolsResponse.tools.length} tools`);
      console.log('   Sample tools:');
      toolsResponse.tools.slice(0, 5).forEach(tool => {
        console.log(`     - ${tool.name}`);
      });
      testsPassed++;
    } catch (error) {
      console.log(`❌ List tools: Failed`);
      console.log(`   Error: ${error.message}`);
      testsFailed++;
    }

    // Print summary
    console.log('\n' + '=' .repeat(50));
    console.log('\n📊 Test Summary:\n');
    console.log(`   Total Tests: ${testsPassed + testsFailed}`);
    console.log(`   ✅ Passed: ${testsPassed}`);
    console.log(`   ❌ Failed: ${testsFailed}`);
    console.log(`   Success Rate: ${((testsPassed / (testsPassed + testsFailed)) * 100).toFixed(1)}%`);
    
    if (testsFailed === 0) {
      console.log('\n🎉 All tests passed successfully!');
    } else {
      console.log('\n⚠️  Some tests failed. Please review the errors above.');
    }

  } catch (error) {
    console.error('\n❌ Fatal error:', error.message);
    console.error('Stack trace:', error.stack);
  } finally {
    // Clean up
    console.log('\n🔧 Cleaning up...');
    try {
      if (client) {
        await client.close();
      }
    } catch (cleanupError) {
      console.error('Error during cleanup:', cleanupError.message);
    }
    console.log('\n' + '=' .repeat(50));
    process.exit(testsFailed > 0 ? 1 : 0);
  }
}

// Run tests
testCoqServer().catch(console.error);