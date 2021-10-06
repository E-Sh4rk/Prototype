FROM ubuntu:20.04

LABEL maintainer="Kim Nguyen <kim.nguyen@universite-paris-saclay.fr>"

ARG DEBIAN_FRONTEND=noninteractive

RUN apt-get update -y && \
 apt-get dist-upgrade -y && \
 apt-get install -y -q \
 locales tzdata ca-certificates sudo ssh git \
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
         libuchardet0 libx11-dev libxau-dev libxcb1-dev libxdmcp-dev \
         linux-libc-dev m4 make man-db pkg-config po-debconf x11proto-core-dev \
         x11proto-dev libcurl4-gnutls-dev libexpat1-dev pkg-config wget unzip

RUN mkdir -p /usr/local/bin && wget -O /usr/local/bin/opam \
            'https://github.com/ocaml/opam/releases/download/2.1.0/opam-2.1.0-x86_64-linux' && \
             chmod 755 /usr/local/bin/opam

RUN echo "Europe/Paris" > /etc/timezone && \
     ln -nsf /usr/share/zoneinfo/Europe/Paris /etc/localtime && \
     sed -i -e 's/# en_US.UTF-8 UTF-8/en_US.UTF-8 UTF-8/' /etc/locale.gen && \
     locale-gen

RUN adduser --disabled-password --gecos "" --shell /bin/bash occtyping

USER occtyping

ARG OPAMYES=true
ARG ocaml_version=4.12.1

RUN opam init  --disable-sandboxing --bare && \
    opam switch create "$ocaml_version" && \
    eval `opam config env`

RUN opam pin -n add cduce-types 'git+https://gitlab.math.univ-paris-diderot.fr/cduce/cduce#polymorphic' && \
    opam pin -n add cduce 'git+https://gitlab.math.univ-paris-diderot.fr/cduce/cduce#polymorphic' && \
    opam install cduce-types cduce pomap ppx_deriving dune js_of_ocaml-compiler js_of_ocaml-ppx markup menhir menhirLib num ocaml ocaml-compiler-libs ocaml-expat ocamlnet ocurl odoc pxp sedlex

RUN opam clean

RUN cd /home/occtyping && \
    git clone https://github.com/E-Sh4rk/Prototype.git && \
    cd Prototype && \
    git checkout -b popl22-AE origin/popl22-AE && \
    cd src && \
    opam exec -- make

ENV TZ "Europe/Paris"
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8

WORKDIR /home/occtyping

ENTRYPOINT [ "opam", "exec", "--" ]

CMD [ "/bin/sh", "-c", "bash" ]
