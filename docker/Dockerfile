FROM ubuntu:latest

ARG USERNAME=user
ARG UID=1000
ARG GID=1000

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && \
    apt-get -y upgrade && \
    apt-get install -y \
      vim \
      build-essential \
      zsh \
      git \
      curl \
      libncurses5-dev \
      opam \
      libgmp-dev \
      pkg-config \
      ca-certificates \
      libffi-dev \
      libffi8ubuntu1 \
      libgmp10 \
      npm \
      procps \
      clang && \
    rm -rf /var/lib/apt/lists/*

RUN cd /tmp && \
    curl -sLJO https://github.com/vprover/vampire/releases/download/v5.0.1/vampire-Linux-X64.zip && \
    unzip vampire-Linux-X64.zip && \
    mv vampire /usr/local/bin

RUN cd /tmp && \
    curl -sLJO https://github.com/CVC4/CVC4-archived/releases/download/1.8/cvc4-1.8-x86_64-linux-opt && \
    mv cvc4-1.8-x86_64-linux-opt /usr/local/bin && \
    chmod +x /usr/local/bin/cvc4

RUN cd /tmp && \
    git clone --depth 1 https://github.com/eprover/eprover.git && \
    cd eprover && \
    ./configure --bindir=/usr/local/bin --man-prefix=/usr/local/share/man && \
    make -j`nproc` && \
    make install

RUN cd /tmp && \
    git clone --depth 1 https://github.com/Z3Prover/z3.git && \
    cd z3 && \
    python3 scripts/mk_make.py --prefix=/usr/local && \
    cd build && \
    make -j`nproc` && \
    make install &&
    make -j`nproc` examples && \
    cp z3_tptp /usr/local/bin

RUN npm i -g @openai/codex

RUN set -eux; \
    OLD_USER_BY_UID="$(getent passwd "${UID}" | cut -d: -f1 || true)"; \
    OLD_GROUP_BY_GID="$(getent group "${GID}" | cut -d: -f1 || true)"; \
    OLD_USER_BY_NAME="$(getent passwd "${USERNAME}" | cut -d: -f1 || true)"; \
    OLD_GROUP_BY_NAME="$(getent group "${USERNAME}" | cut -d: -f1 || true)"; \
    \
    if [ -n "${OLD_USER_BY_UID}" ]; then \
        userdel -r "${OLD_USER_BY_UID}" || userdel "${OLD_USER_BY_UID}" || true; \
    fi; \
    \
    if [ -n "${OLD_USER_BY_NAME}" ] && [ "${OLD_USER_BY_NAME}" != "${OLD_USER_BY_UID}" ]; then \
        userdel -r "${OLD_USER_BY_NAME}" || userdel "${OLD_USER_BY_NAME}" || true; \
    fi; \
    \
    if [ -n "${OLD_GROUP_BY_GID}" ]; then \
        groupdel "${OLD_GROUP_BY_GID}" || true; \
    fi; \
    \
    if [ -n "${OLD_GROUP_BY_NAME}" ] && [ "${OLD_GROUP_BY_NAME}" != "${OLD_GROUP_BY_GID}" ]; then \
        groupdel "${OLD_GROUP_BY_NAME}" || true; \
    fi; \
    \
    groupadd -g "${GID}" "${USERNAME}"; \
    useradd -m -d "/home/${USERNAME}" -s /bin/zsh -u "${UID}" -g "${GID}" "${USERNAME}"; \
    mkdir -p "/home/${USERNAME}"; \
    chown -R "${UID}:${GID}" "/home/${USERNAME}"

COPY zshrc /tmp/.zshrc
COPY zshenv /tmp/.zshenv

RUN cp /tmp/.zshrc "/home/${USERNAME}/.zshrc" && \
    cp /tmp/.zshenv "/home/${USERNAME}/.zshenv" && \
    chown "${UID}:${GID}" "/home/${USERNAME}/.zshrc" "/home/${USERNAME}/.zshenv"

USER ${USERNAME}
WORKDIR /home/${USERNAME}
ENV HOME=/home/${USERNAME}

RUN whoami && id && echo "HOME=$HOME"

RUN opam init --yes --auto-setup && \
    eval $(opam env)

RUN opam repo add rocq-released https://rocq-prover.org/opam/released && \
    opam update && \
    opam install -y rocq-prover rocq-stdlib vsrocq-language-server rocq-core=9.1.1 coq-hammer

RUN curl -fsSL https://claude.ai/install.sh | bash

RUN echo "[[ ! -r '${HOME}/.opam/opam-init/init.zsh' ]] || source '${HOME}/.opam/opam-init/init.zsh' > /dev/null 2> /dev/null" >> .zshenv

RUN curl -fsSL https://gh.io/copilot-install | bash

RUN opam repo add coq-released https://coq.inria.fr/opam/released && opam install -y rocq-stdpp

RUN curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | \
    BOOTSTRAP_HASKELL_NONINTERACTIVE=1 \
    BOOTSTRAP_HASKELL_GHC_VERSION=latest \
    BOOTSTRAP_HASKELL_CABAL_VERSION=latest \
    BOOTSTRAP_HASKELL_INSTALL_STACK=1 \
    BOOTSTRAP_HASKELL_INSTALL_HLS=1 \
    BOOTSTRAP_HASKELL_ADJUST_BASHRC=P sh

RUN . "/home/${USERNAME}"/.ghcup/env && stack install crypton cborg

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y

RUN . "/home/${USERNAME}"/.cargo/env && \
    cargo install cargo-binutils && \
    cargo install mdbook-mermaid

CMD ["/bin/zsh"]
