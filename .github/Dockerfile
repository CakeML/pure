FROM ubuntu:20.04

WORKDIR /home

# Install pre-requisites
RUN apt-get update && \
    apt-get install -y git build-essential gcc-10 libffi-dev wget mlton

# Install PolyML
RUN git clone https://github.com/polyml/polyml.git && cd polyml && \
    git checkout fixes-5.9 && \
    ./configure --prefix=/usr && \
    make && \
    make install

# Create user
ARG USERNAME=pure
RUN mkdir /etc/sudoers.d && \
    adduser --shell /bin/bash --disabled-password --gecos "" $USERNAME && \
    echo "$USERNAME ALL=(ALL) NOPASSWD: ALL" > /etc/sudoers.d/$USERNAME && \
    chmod 0440 /etc/sudoers.d/$USERNAME

# Switch to user
USER $USERNAME
ENV WORKDIR /home/$USERNAME
WORKDIR $WORKDIR

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

# Set up entrypoint
RUN echo "export PS1='\u:\w \$ '" > /home/$USERNAME/.bashrc
ENTRYPOINT ["bash"]

