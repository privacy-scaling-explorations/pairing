FROM ubuntu:22.04

WORKDIR /app

COPY . .

# rust path
ENV PATH=$PATH:/root/.cargo/bin

RUN apt-get update -y &&\
    apt-get install build-essential curl -y

# enable rust
RUN curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain nightly-2021-11-17
