include ../Makefile.config

COQARG=-I ./ott -I ./monads -I $(METALIB) -I ./compcert -I ./GraphBasics \
	-impredicative-set

all:
	+make -C $(METALIB)
	+make -C ./monads
	+make -C ./ott
	+make -C ./compcert 
	+make -C ./GraphBasics
	+make ott 
#	+make -C ./llvm_op

ott: main.pdf typings.vo interpreter.vo opsem_inst.vo vellvm.vo opsem_dom.vo

infrastructure_aux.vo : infrastructure_aux.v syntax.vo targetdata.vo \
	compcert/Kildall.vo
	$(COQC) $(COQARG) infrastructure_aux.v

syntax.vo : ./monads/monad.vo ./compcert/Floats.vo ./compcert/alist.vo \
	./compcert/Memory.vo syntax.v
	$(COQC) $(COQARG) syntax.v

syntax.v : syntax.ott 
	$(OTT) -coq_expand_list_types true -i syntax.ott -o syntax.v
	./fixott.py syntax.v

infrastructure.ott : infrastructure_aux.vo syntax.ott coq2ott.py 
	./coq2ott.py
	cp merge.ott infrastructure.ott       

m_typings.ott : typings.ott spanlines.py
	./spanlines.py typings.ott

infrastructure.v typings.v: syntax.ott infrastructure_aux.vo \
	infrastructure.ott m_typings.ott ./monads/monad.vo targetdata.vo
	$(OTT) -merge false -coq_expand_list_types true \
            -i syntax.ott -o _tmp_syntax.v \
	    -i infrastructure.ott -o infrastructure.v \
	    -i m_typings.ott -o typings.v
	rm _tmp_syntax.v
	./fixott.py infrastructure.v
	./fixott.py typings.v

infrastructure.vo: infrastructure.v
	$(COQC) $(COQARG) infrastructure.v

typings.vo: typings.v infrastructure.vo analysis.vo
	$(COQC) $(COQARG) typings.v

targetdata.vo: targetdata.v syntax.vo
	$(COQC) $(COQARG) targetdata.v

analysis.vo: compcert/Kildall.vo analysis.v infrastructure.vo \
	infrastructure_props.vo compcert/Memory.vo GraphBasics/Dipaths.vo
	$(COQC) $(COQARG) analysis.v

genericvalues.vo: syntax.vo infrastructure.vo compcert/tactics.vo \
	compcert/trace.vo genericvalues.v targetdata.vo compcert/Memory.vo
	$(COQC) $(COQARG) genericvalues.v

interpreter.vo: interpreter.v syntax.vo infrastructure.vo genericvalues.vo \
	infrastructure_props.vo dopsem.vo
	$(COQC) $(COQARG) interpreter.v

infrastructure_props.vo: infrastructure_props.v syntax.vo infrastructure.vo \
	compcert/Kildall.vo
	$(COQC) $(COQARG) infrastructure_props.v

typings_props.vo: typings_props.v syntax.vo infrastructure.vo genericvalues.vo \
	infrastructure_props.vo analysis.vo typings.vo
	$(COQC) $(COQARG) typings_props.v

opsem.vo: opsem.v typings_props.vo syntax.vo infrastructure.vo \
	genericvalues.vo infrastructure_props.vo
	$(COQC) $(COQARG) opsem.v

opsem_props.vo: opsem_props.v opsem.vo syntax.vo infrastructure.vo \
	genericvalues.vo infrastructure_props.vo
	$(COQC) $(COQARG) opsem_props.v

opsem_wf.vo: opsem_wf.v opsem_props.vo opsem.vo syntax.vo infrastructure.vo\
       genericvalues.vo infrastructure_props.vo
	$(COQC) $(COQARG) opsem_wf.v

opsem_dom.vo: opsem_dom.v opsem_wf.vo
	$(COQC) $(COQARG) opsem_dom.v

dopsem.vo: dopsem.v opsem_wf.vo
	$(COQC) $(COQARG) dopsem.v

ndopsem.vo: ndopsem.v opsem_wf.vo
	$(COQC) $(COQARG) ndopsem.v

opsem_inst.vo: opsem_inst.v ndopsem.vo dopsem.vo syntax.vo infrastructure.vo
	$(COQC) $(COQARG) opsem_inst.v

def.tex: syntax.ott infrastructure.ott m_typings.ott main.tex 
	$(OTT) -merge false -o def.tex \
          -tex_show_meta false \
          -tex_wrap false \
            syntax.ott infrastructure.ott m_typings.ott

vellvm.vo : vellvm.v syntax.vo infrastructure_props.vo typings_props.vo \
	targetdata.vo dopsem.vo ndopsem.vo
	$(COQC) $(COQARG) vellvm.v

main.pdf: def.tex main.tex macros.sty 
	pdflatex main.tex
	pdflatex main.tex

clean: 
	+make -C ./ott clean
	+make -C ./compcert clean
	+make -C ./monads clean	
	+make -C ./llvm_op clean
	rm -rf main.pdf main.log main.aux main.log syntax.v infrastructure.v \
		typings.vo *.vo *.glob merge.ott m_*.ott

