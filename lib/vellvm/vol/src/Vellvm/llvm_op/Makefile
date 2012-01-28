
include ../../Makefile.config

COQARG=-I .. -I ../ott -I ../monads -I $(METALIB) -I ../compcert

all: main.pdf ssa_verifier.vo ssa_executionengine.vo ssa_all.vo

m_ssa_verifier.ott : ssa_verifier.ott ../spanlines.py
	../spanlines.py ssa_verifier.ott

ssa_def.v ssa_lib.v: ../ssa_def.ott ../ssa_coq.ott ../ssa_lib.ott emacs.ott ../ssa_def.v ../ssa_coq_lib.vo ../monads/monad.vo m_ssa_verifier.ott ssa_interpreter.ott
	$(OTT) -merge false -coq_expand_list_types true \
            -i ../ssa_def.ott -o ssa_def.v \
	    -i ../ssa_coq.ott -i ../ssa_lib.ott -o ssa_lib.v \
	    -i m_ssa_verifier.ott -i ssa_interpreter.ott -o ssa_all.v
	../fixott.py ssa_def.v	
	../fixott.py ssa_lib.v	
	../fixott.py ssa_all.v	

ssa_def.vo: ssa_def.v
	$(COQC) $(COQARG) ssa_def.v

ssa_lib.vo: ssa_lib.v ssa_def.vo
	$(COQC) $(COQARG) ssa_lib.v

ssa_all.vo: ssa_all.v ssa_def.vo ssa_lib.vo
	$(COQC) $(COQARG) ssa_all.v

ssa_verifier.vo: ssa_verifier.v ../ssa_def.vo ../ssa_lib.vo ../monads/monad.vo ssa_def.vo ssa_lib.vo
	$(COQC) $(COQARG) ssa_verifier.v

ssa_executionengine.vo: ssa_executionengine.v ../ssa_def.vo ../ssa_lib.vo ../monads/monad.vo ssa_def.vo ssa_lib.vo
	$(COQC) $(COQARG) ssa_executionengine.v

ssa.tex: ../ssa_def.ott ../ssa_coq.ott ../ssa_lib.ott m_ssa_verifier.ott ssa_interpreter.ott omain.tex 
	$(OTT) -merge false -o ssa.tex \
          -tex_show_meta false \
          -tex_wrap false \
          -tex_filter omain.tex main.tex \
            ../ssa_def.ott ../ssa_coq.ott ../ssa_lib.ott m_ssa_verifier.ott ssa_interpreter.ott

main.pdf: ssa.tex main.tex macros.sty 
	pdflatex main.tex
	pdflatex main.tex

clean: 
	rm -rf ssa.tex main.pdf main.log main.aux main.log main.tex ssa_all.v ssa_def.v ssa_lib.v *.vo *.glob merge.ott m_*.ott

