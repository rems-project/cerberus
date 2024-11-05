# Build image with all dependencies
FROM ubuntu:22.04 as deps

RUN apt-get update
RUN apt-get upgrade -y
RUN apt-get install -y opam libgmp-dev libmpfr-dev

ENV OPAMCONFIRMLEVEL=unsafe-yes
RUN opam init --disable-sandboxing
RUN opam install dune lem

ADD . /opt/cerberus
WORKDIR /opt/cerberus
RUN opam install --deps-only  ./cerberus-lib.opam ./cn.opam
RUN eval `opam env` \
  && make install \
  && make install_cn

WORKDIR /opt

COPY docker_entry_point.sh /opt/docker_entry_point.sh
RUN chmod +x /opt/docker_entry_point.sh
WORKDIR /data
ENTRYPOINT ["/opt/docker_entry_point.sh"]
