FROM icp-base:oopsla25 
WORKDIR /home/build/icp-fiat
COPY --chown=opam:opam . /home/build/icp-fiat
RUN echo "Building Fiat example..." && \
    eval "$(opam env)" && \
    make src/Examples/Tutorial/Queue.vo

CMD ["bash"]
