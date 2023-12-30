FROM --platform=linux/amd64 ghcr.io/cakeml/pure@sha256:50da19b007e0cc2693db68f98ab339f10c0df8776c7cc1fd5724cf89677ea930

# Checkout artifact branch
RUN cd ~/pure && git fetch && git checkout origin/esop24-artifact

# Remove git files
RUN rm -rf ~/pure/.git ~/pure/.github

# Pull in CakeML compiler
RUN cd ~/pure/examples && make lib/cake.S

# Replace identifying files
RUN cp ~/pure/anonymised/examples-Makefile ~/pure/examples/Makefile

# Cleanup: removed `anonymised` directory
RUN rm -rf ~/pure/anonymised

ENTRYPOINT ["bash"]

