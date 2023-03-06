FROM ghcr.io/cakeml/pure@sha256:0bb91cfb3646193d0f53beeca59578f2e7ccfa482b9b49dc09c0ec190fe62405

# Checkout artifact branch
RUN cd ~/pure && git fetch && git checkout origin/pldi23-artifact

# Remove git files
RUN rm -rf ~/hol/.git ~/cakeml/.git ~/pure/.git ~/pure/.github

# Pull in CakeML compiler
RUN cd ~/pure/examples && make lib/cake.S

# Remove/replace identifying files
RUN rm -f ~/hol/CONTRIBUTORS
RUN cp ~/pure/anonymised/cakeml-COPYING ~/cakeml/COPYING
RUN cp ~/pure/anonymised/examples-Makefile ~/pure/examples/Makefile

# Cleanup: removed `anonymised` directory
RUN rm -rf ~/pure/anonymised

ENTRYPOINT ["bash"]

