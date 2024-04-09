# -------------
# OS Base Image
# -------------
# >> Includes system-wide dependencies
FROM ubuntu:20.04 as lib-base
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update && \
    apt-get -y --no-install-recommends install \
        cmake \
        make \
        clang \
        g++ \
        curl \
        default-jdk \
        python3 \
        python3-setuptools \
        python-is-python3 \
        vim \
        python3-pip \
        sudo
RUN pip install tabulate

# # ----------------
# # AriParti Builder Image
# # ----------------
# # >> Includes build files and compiles the basic AriParti sources
FROM lib-base as builder
RUN mkdir /AriParti/
RUN mkdir /AriParti/AE-test-output
COPY ./benchmark-lists/ /AriParti/benchmark-lists/
# COPY ./benchmarks/ /AriParti/benchmarks/
COPY ./bin/ /AriParti/bin/
COPY ./src/ /AriParti/src/
COPY ./scripts/ /AriParti/scripts/
