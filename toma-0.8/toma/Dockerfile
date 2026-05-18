FROM alpine:latest

RUN apk add --no-cache \
    ghc \
    cabal \
    musl-dev \
    gmp-dev \
    gmp-static \
    zlib-dev \
    zlib-static \
    ncurses-dev \
    libffi-dev \
    git \
    build-base

RUN cabal update

WORKDIR /app

COPY toma.cabal .

RUN cabal build --only-dependencies

COPY . .

RUN cabal build --enable-executable-static \
    --ghc-options="-optl-static -optl-pthread -optl-lm -optl-ldl -optl-lrt -optl-lgmp -optl-lffi"

FROM scratch
COPY --from=0 /app/dist-newstyle/build/x86_64-linux/ghc-*/toma-*/x/toma/build/toma/toma /toma-static
