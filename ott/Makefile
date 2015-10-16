SHELL := /bin/bash

TARGETS :=\
Common.v \
MapsExt.v \
AilTypes.v \
AilSyntax.v \
Range.v \
Implementation.v \
AilTypesAux.v \
AilAux.v


%_.ott:
	rm -f $@
	touch $@
	$(eval DEP := $(shell cat $*.dep 2> /dev/null | tr "\n" " "))
	$(eval GRM := $(shell cat $*.grm 2> /dev/null | tr "\n" " "))
	for D in $(DEP); do                            \
	  if [ -f "$$D.preamble" ]; then               \
	    cat $$D.preamble |                         \
	    sed 's/^% INC?.*$$/{{ phantom }}/g'        \
	    >> $@ ;                                    \
	  fi ;                                         \
	done
	if [ -f "$*.preamble" ]; then                  \
	  cat $*.preamble |                            \
	  sed 's/^% INC?//g'                           \
	  >> $@ ;                                      \
	fi
	echo "grammar" >> $@
	for G in terminals formula $(GRM); do          \
	  cat $$G.pgrm >> $@ ;                         \
	  if [ -f "$*.$$G" ]; then                     \
	    cat $*.$$G >> $@ ;                         \
	  fi ;                                         \
	  for D in $(DEP); do                          \
	    if [ -f "$$D.$$G" ]; then                  \
	      cat $$D.$$G >> $@ ;                      \
	    fi ;                                       \
	  done ;                                       \
	done
	for D in $(DEP); do                            \
	  if [ -f "$$D.grammar" ]; then                \
	    cat $$D.grammar |                          \
	    sed 's/^% INC?.*$$/{{ phantom }}/g'        \
	    >> $@ ;                                    \
	  fi ;                                         \
	done
	if [ -f "$*.grammar" ]; then                   \
	  cat $*.grammar |                             \
	  sed 's/^% INC?//g'                           \
	  >> $@ ;                                      \
	fi
	for D in $(DEP); do                            \
	  if [ -f "$$D.defns" ]; then                  \
	    echo "embed {{coq %BEGIN_IMPORT}}" >> $@ ; \
	    cat $$D.defns >> $@ ;                      \
	    echo "embed {{coq %END_IMPORT}}" >> $@ ;   \
	  fi ;                                         \
	done
	if [ -f "$*.defns" ]; then                     \
	  cat $*.defns >> $@ ;                         \
	fi

%.v: %_.ott
	ott -coq_expand_list_types false -coq_avoid 0 -i $*_.ott -o coq/$@
	perl -i -0pe 's/%BEGIN_IMPORT((\n|.)*?)%END_IMPORT//g' coq/$@
	cd coq && coqtop -I ../../../ott/coq -compile $*

coq : ${TARGETS}
