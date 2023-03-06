FROM ubuntu:latest

ENV WORKDIR /home
WORKDIR $WORKDIR

# Install pre-requisites
RUN apt-get update && \
    apt-get install -y git build-essential gcc-10 libffi-dev wget

# Install PolyML
RUN git clone https://github.com/polyml/polyml.git && cd polyml && \
    git checkout fixes-5.9 && \
    ./configure --prefix=/usr && \
    make && \
    make install

# Build HOL
RUN git clone https://github.com/hol-theorem-prover/hol.git && cd hol && \
    poly < tools/smart-configure.sml && \
    ./bin/build

# Clone PureCake and CakeML
RUN git clone https://github.com/cakeml/cakeml && \
    git clone https://github.com/cakeml/pure

# Update environment variables
ENV HOLDIR $WORKDIR/hol/bin
ENV PATH $HOLDIR:$PATH
ENV CAKEMLDIR $WORKDIR/cakeml
ENV PUREDIR $WORKDIR/pure

# Build PureCake and necessary dependencies
RUN cd pure && Holmake

# Build PureLang sample programs
RUN cd pure/examples && make check

ENTRYPOINT ["bash"]
