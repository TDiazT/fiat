FROM debian:buster-slim

# Install dependencies
RUN apt-get update && apt-get install -y \
    curl \
    sudo \
    git \
    build-essential \
    m4 \
    opam \
    ca-certificates \
    python2.7 \
    python2.7-dev \
    python-pip \
    && rm -rf /var/lib/apt/lists/*

# Initialize OPAM and set up OCaml 4.02.3
RUN opam init -a --disable-sandboxing --compiler=4.02.3 && \
    eval $(opam env) && \
    opam update

# Install Coq 8.4.6
RUN eval $(opam env) && \
    opam repo add coq-released https://coq.inria.fr/opam/released && \
    opam update && \
    opam install -y coq.8.4.6

# Set the default OCaml switch
RUN opam switch 4.02.3 && eval $(opam env)

# Add opam environment setup to .bashrc
RUN echo 'eval $(opam env)' >> /root/.bashrc

# Set the entry point to bash
ENTRYPOINT ["bash", "-c"]

# Run eval $(opam env) when the container starts
CMD ["eval $(opam env) && exec bash"]