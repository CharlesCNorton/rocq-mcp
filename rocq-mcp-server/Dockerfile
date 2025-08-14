# Multi-stage build for MCP Coq Server
FROM ocaml/opam:ubuntu-22.04-ocaml-4.14 AS coq-builder

# Install system dependencies
USER root
RUN apt-get update && apt-get install -y \
    build-essential \
    git \
    curl \
    wget \
    m4 \
    unzip \
    libgmp-dev \
    libssl-dev \
    pkg-config \
    python3 \
    python3-pip \
    && rm -rf /var/lib/apt/lists/*

# Switch to opam user
USER opam

# Initialize OPAM and install Coq
RUN opam init --disable-sandboxing --yes && \
    eval $(opam env) && \
    opam update && \
    opam install -y coq.8.18.0

# Install core Coq libraries
RUN eval $(opam env) && \
    opam install -y \
    coq-mathcomp-ssreflect.2.1.0 \
    coq-mathcomp-algebra \
    coq-mathcomp-field \
    coq-mathcomp-fingroup \
    coq-mathcomp-solvable \
    coq-mathcomp-character

# Install theorem proving tools
RUN eval $(opam env) && \
    opam install -y \
    coq-equations.1.3+8.18 \
    coq-ltac2.1.2.0+8.18 \
    coq-elpi.2.0.2 \
    coq-hierarchy-builder

# Install verification libraries
RUN eval $(opam env) && \
    opam install -y \
    coq-stdpp.1.9.0 \
    coq-iris.4.1.0 \
    coq-iris-heap-lang

# Install mathematical libraries
RUN eval $(opam env) && \
    opam install -y \
    coq-coquelicot.3.4.0 \
    coq-flocq.4.1.3 \
    coq-interval.4.9.0 \
    coq-gappa.1.5.4

# Install automation tools (if available)
RUN eval $(opam env) && \
    opam install -y \
    coq-hammer || true && \
    opam install -y \
    coq-quickchick || true

# Install additional useful libraries
RUN eval $(opam env) && \
    opam install -y \
    coq-ext-lib.0.11.8 \
    coq-simple-io.1.8.0 \
    coq-coqprime.1.3.0 \
    coq-bignums.9.0.0+coq8.18 \
    coq-zorns-lemma.10.2.0 \
    coq-topology.10.2.0

# Install CompCert (if available for the platform)
RUN eval $(opam env) && \
    opam install -y coq-compcert || true

# Install MetaCoq
RUN eval $(opam env) && \
    opam install -y \
    coq-metacoq-template.1.2.1+8.18 \
    coq-metacoq-pcuic.1.2.1+8.18 \
    coq-metacoq-safechecker.1.2.1+8.18 \
    coq-metacoq-erasure.1.2.1+8.18 || true

# Install HoTT (if compatible)
RUN eval $(opam env) && \
    opam install -y coq-hott || true

# Install UniMath (if compatible)
RUN eval $(opam env) && \
    opam install -y coq-unimath || true

# Install CoqEAL
RUN eval $(opam env) && \
    opam install -y \
    coq-coqeal.2.0.1 || true

# Install CoRN
RUN eval $(opam env) && \
    opam install -y coq-corn || true

# Install Fiat-Crypto (from source if needed)
RUN eval $(opam env) && \
    cd /tmp && \
    git clone https://github.com/mit-plv/fiat-crypto.git && \
    cd fiat-crypto && \
    git submodule update --init --recursive && \
    make -j$(nproc) || true

# Final stage with Node.js
FROM ubuntu:22.04

# Install runtime dependencies
RUN apt-get update && apt-get install -y \
    curl \
    git \
    build-essential \
    libgmp-dev \
    python3 \
    python3-pip \
    && rm -rf /var/lib/apt/lists/*

# Install Node.js 20
RUN curl -fsSL https://deb.nodesource.com/setup_20.x | bash - && \
    apt-get install -y nodejs && \
    rm -rf /var/lib/apt/lists/*

# Copy OPAM installation from builder
COPY --from=coq-builder /home/opam/.opam /opt/opam
COPY --from=coq-builder /home/opam/.opam/4.14.1/bin/* /usr/local/bin/

# Set up OPAM environment variables
ENV OPAMROOT=/opt/opam
ENV PATH="/opt/opam/4.14.1/bin:${PATH}"
ENV CAML_LD_LIBRARY_PATH="/opt/opam/4.14.1/lib/stublibs:/opt/opam/4.14.1/lib/ocaml/stublibs:/opt/opam/4.14.1/lib/ocaml"
ENV OCAML_TOPLEVEL_PATH="/opt/opam/4.14.1/lib/toplevel"
ENV MANPATH="/opt/opam/4.14.1/man:${MANPATH}"

# Create app directory
WORKDIR /app

# Copy package files
COPY package*.json ./
COPY tsconfig.json ./

# Install Node dependencies
RUN npm ci

# Copy source code
COPY src ./src

# Build the TypeScript application
RUN npm run build

# Copy additional files
COPY README.md ./

# Create a directory for Coq projects
RUN mkdir -p /workspace

# Set working directory for Coq projects
WORKDIR /workspace

# Environment variables for the MCP server
ENV NODE_ENV=production
ENV LOG_LEVEL=info

# Health check
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD node -e "console.log('OK')" || exit 1

# Default command
CMD ["node", "/app/dist/index.js"]

# Labels
LABEL maintainer="MCP Coq Server"
LABEL description="MCP server for Coq/Rocq theorem proving with comprehensive OPAM library support"
LABEL version="1.0.0"

# Expose volume for workspace
VOLUME ["/workspace"]