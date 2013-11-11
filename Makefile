ifeq (${COMMON},)
$(warning "Must set the common directory. Source the develop script at the root of the repository or set the COMMON environment variable")
ROOT=../../
COMMON=${ROOT}/apps/common
endif

include ${COMMON}/Makefile.inc

GHCINC= ${TSL2_PATH} ${UTIL_PATH} .
LIBSiiii=
LIBPATHS= 
TARGET=test.hs
CLIBS=
GHC_FLAGS+=-o ./test -Wall #-fforce-recomp # -prof -auto-all -rtsopts # -fforce-recomp 

CABAL_PACKAGES= 

EXTRA_LIB_DIRS=

cabal: 
	cabal-dev install $(CABAL_PACKAGES) $(EXTRA_LIB_DIRS)
	cp cabal-dev/bin/cwtest ./cwtest

default:
	ghc --make -c -fcontext-stack=64 -O2 ${GHC_FLAGS} ${GHCINC:%=-i%} ${TARGET} ${LIBPATHS:%=-L%} ${LIBS:%=-l%}
	ghc --make -fcontext-stack=64    -O2 ${GHC_FLAGS} ${GHCINC:%=-i%} ${TARGET} ${LIBPATHS:%=-L%} ${LIBS:%=-l%} ${CLIBS:%=-optl-l%} 

prof:
	ghc --make -c -fcontext-stack=64 -O2 ${GHC_FLAGS} ${GHCINC:%=-i%} ${TARGET} ${LIBPATHS:%=-L%} ${LIBS:%=-l%}
	ghc --make -c -fcontext-stack=64 -osuf oprof -prof -auto-all -rtsopts -O2 ${GHC_FLAGS} ${GHCINC:%=-i%} ${TARGET} ${LIBPATHS:%=-L%} ${LIBS:%=-l%}
	ghc --make -fcontext-stack=64 -osuf oprof -prof -auto-all -rtsopts -O2 ${GHC_FLAGS} ${GHCINC:%=-i%} ${TARGET} ${LIBPATHS:%=-L%} ${LIBS:%=-l%} ${CLIBS:%=-optl-l%} 
