FROM ubuntu
RUN apt-get update
RUN apt-get upgrade -y
RUN apt-get install -y opam libgmp-dev libmpfr-dev
RUN mkdir /etc/sudoers.d/ && \
  echo 'opam ALL=(ALL:ALL) NOPASSWD:ALL' > /etc/sudoers.d/opam && \
  chmod 440 /etc/sudoers.d/opam && \
  chown root:root /etc/sudoers.d/opam && \
  adduser --disabled-password --gecos '' opam && \
  passwd -l opam && \
  chown -R opam:opam /home/opam
USER opam
ENV HOME /home/opam
WORKDIR /home/opam
RUN opam init --disable-sandboxing
RUN eval `opam env` && \
  opam repository add rems https://github.com/rems-project/opam-repository.git && \
  opam install -y ocamlfind ocamlbuild pprint yojson ppx_sexp_conv sexplib ppx_deriving cmdliner menhir z3 dune lem sha apron
COPY --chown=opam . /home/opam/cerberus-private/
RUN eval `opam env` && \
  cd /home/opam/cerberus-private/ && \
  make && \
  make install
COPY --chown=opam docker_entry_point.sh /home/opam/
RUN chmod +x docker_entry_point.sh
WORKDIR /data
ENTRYPOINT ["/home/opam/docker_entry_point.sh"]
