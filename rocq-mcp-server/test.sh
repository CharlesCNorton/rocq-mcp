#!/bin/bash

# Simple test script for MCP Coq Server

echo "MCP Coq Server Test Script"
echo "=========================="
echo

# Check if Coq is installed
echo "Checking Coq installation..."
if command -v coqc &> /dev/null; then
    echo "✓ Coq is installed:"
    coqc --version
else
    echo "✗ Coq is not installed. Please install Coq first."
    echo "  Run: opam install coq"
    exit 1
fi
echo

# Check if Node.js is installed
echo "Checking Node.js installation..."
if command -v node &> /dev/null; then
    echo "✓ Node.js is installed:"
    node --version
else
    echo "✗ Node.js is not installed. Please install Node.js first."
    exit 1
fi
echo

# Install dependencies if needed
if [ ! -d "node_modules" ]; then
    echo "Installing npm dependencies..."
    npm install
    echo
fi

# Build the project
echo "Building the project..."
npm run build
echo

# Test Coq file compilation
echo "Testing Coq file compilation..."
if [ -f "examples/basic_proof.v" ]; then
    coqc examples/basic_proof.v
    if [ $? -eq 0 ]; then
        echo "✓ Coq file compiled successfully"
        rm -f examples/*.vo examples/*.glob examples/*.vok examples/*.vos
    else
        echo "✗ Coq file compilation failed"
    fi
else
    echo "⚠ Test file not found: examples/basic_proof.v"
fi
echo

# Check OPAM packages
echo "Checking installed Coq packages..."
if command -v opam &> /dev/null; then
    echo "Installed Coq packages:"
    opam list | grep coq- | head -10
    echo "..."
else
    echo "⚠ OPAM not found. Cannot list Coq packages."
fi
echo

echo "Setup complete! You can now:"
echo "1. Start the server: npm start"
echo "2. Run the test client: node examples/test_client.js"
echo "3. Use with your MCP client by adding to config:"
echo '   {
     "mcpServers": {
       "coq": {
         "command": "node",
         "args": ["'$(pwd)'/dist/index.js"]
       }
     }
   }'