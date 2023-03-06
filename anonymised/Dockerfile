FROM ghcr.io/cakeml/pure:master

# Checkout artifact branch
RUN cd pure && git checkout pldi23-artifact

# Remove git files
RUN rm -rf hol/.git cakeml/.git pure/.git pure/.github

# Pull in CakeML compiler
RUN cd pure/examples && make lib/cake.S

# Remove/replace identifying files
RUN rm -f hol/CONTRIBUTORS
RUN cp pure/anonymised/cakeml-COPYING cakeml/COPYING
RUN cp pure/anonymised/examples-Makefile examples/Makefile

# Cleanup: removed `anonymised` directory
RUN rm -rf pure/anonymised

ENTRYPOINT ["bash"]

