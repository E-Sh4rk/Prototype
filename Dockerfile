FROM ubuntu:20.04
LABEL maintainer="Kim Nguyen <kim.nguyen@universite-paris-saclay.fr>"

ARG poly_version=1.0.2


RUN apt-get update -y && \
 apt-get dist-upgrade -y && \
 DEBIAN_FRONTEND=noninteractive apt-get install -y -q \
 locales tzdata ca-certificates sudo git nano emacs-nox vim \
         autoconf automake autopoint autotools-dev binutils binutils-common \
         binutils-dev binutils-x86-64-linux-gnu bsdmainutils build-essential \
         cpp cpp-9 dwz g++ g++-9 gcc gcc-9 gcc-9-base gettext gettext-base \
         groff-base intltool-debian libarchive-zip-perl libasan5 libatomic1 \
         libbinutils libc-dev-bin libc6-dev libcc1-0 libcroco3 libcrypt-dev \
         libctf-nobfd0 libctf0 libdebhelper-perl libdpkg-perl libelf1 \
         libfile-stripnondeterminism-perl libgcc-9-dev libgomp1 libiberty-dev\
         libisl22 libitm1 liblsan0 libmpc3 libmpfr6 libncurses-dev \
         libncurses5-dev libpipeline1 libpthread-stubs0-dev libquadmath0 \
         libsigsegv2 libstdc++-9-dev libsub-override-perl libtool libtsan0 libubsan1\
         libuchardet0 linux-libc-dev m4 make man-db pkg-config po-debconf \
         libcurl4-gnutls-dev libssl-dev libexpat1-dev pkg-config python3 wget unzip gnupg
RUN mkdir -p /etc/apt/keyrings
RUN wget -q -nd -O - https://deb.nodesource.com/gpgkey/nodesource-repo.gpg.key | \
    	 gpg --dearmor -o /etc/apt/keyrings/nodesource.gpg
RUN echo "deb [signed-by=/etc/apt/keyrings/nodesource.gpg] https://deb.nodesource.com/node_20.x nodistro main" | tee /etc/apt/sources.list.d/nodesource.list
RUN apt-get update -y &&  DEBIAN_FRONTEND=noninteractive apt-get install -y -q nodejs && apt-get clean
RUN mkdir -p /usr/local/bin && wget -O /usr/local/bin/opam \
            'https://github.com/ocaml/opam/releases/download/2.1.5/opam-2.1.5-x86_64-linux' && \
             chmod 755 /usr/local/bin/opam

RUN echo "Europe/Paris" > /etc/timezone && \
     ln -nsf /usr/share/zoneinfo/Europe/Paris /etc/localtime && \
     sed -i -e 's/# en_US.UTF-8 UTF-8/en_US.UTF-8 UTF-8/' /etc/locale.gen && \
     locale-gen

RUN adduser --disabled-password --gecos "" --shell /bin/bash poly

USER poly

ARG OPAMYES=true
ARG ocaml_version=4.14.1
ARG packages="conf-libssl dune js_of_ocaml-compiler js_of_ocaml-ppx markup menhir menhirLib num ocaml ocaml-compiler-libs ocaml-expat ocamlfind ocamlnet ocurl odoc pomap  ppx_deriving pxp sedlex tsort yojson"


ENV HOME "/home/poly"
WORKDIR "/home/poly"

RUN opam init  --disable-sandboxing --bare && \
    opam switch create "$ocaml_version" && \
    eval `opam config env` && \
    opam install -y ${packages} && \
    opam clean

RUN echo 'test -r $HOME/.opam/opam-init/init.sh && . $HOME/.opam/opam-init/init.sh > /dev/null 2> /dev/null || true' >> "$HOME"/.bashrc

RUN eval "$(opam config env)" && \
    wget -O "Prototype-${poly_version}.tar.gz" -nd "https://github.com/E-Sh4rk/Prototype/archive/refs/tags/v${poly_version}.tar.gz" && \
    tar xf Prototype-${poly_version}.tar.gz && \
    rm -f Prototype-${poly_version}.tar.gz && \
    ln -s Prototype-${poly_version} Prototype && \
    cd Prototype/src && \
    wget -nd https://gitlab.math.univ-paris-diderot.fr/cduce/cduce/-/archive/popl24ae/cduce-popl24ae.tar.gz && \
    tar xf cduce-popl24ae.tar.gz && \
    rm -f cduce-popl24ae.tar.gz && \
    make build libjs && \
    cd ../webeditor && \
    npm ci

ENV TZ "Europe/Paris"
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8

ENTRYPOINT [ "python3", "-m", "http.server", "--directory", "/home/poly/Prototype/webeditor", "9090"  ]
