include ../Makefile.config

VELLVM=../Vellvm

COQARG=-I $(VELLVM)/ott -I $(VELLVM)/monads -I $(VELLVM)/compcert \
	-I $(VELLVM)/GraphBasics -I $(METALIB) -I ./ -impredicative-set

DEPS=$(VELLVM)/monads/monad.vo $(VELLVM)/coq2ott.py $(VELLVM)/coq2ott.py \
	$(VELLVM)/compcert/Memory.vo $(VELLVM)/compcert/alist.vo \
	$(VELLVM)/compcert/tactics.vo $(VELLVM)/compcert/trace.vo \
	$(VELLVM)/compcert/Kildall.vo $(VELLVM)/GraphBasics/Dipaths.vo

all:
	+make ott 

ott: main.pdf typings.vo opsem_wf.vo interpreter.vo vminus.vo subst.vo \
	removal.vo vsubst.vo inssa.vo motion.vo

infrastructure_aux.vo : infrastructure_aux.v syntax.vo $(DEPS)
	$(COQC) $(COQARG) infrastructure_aux.v

inssa.vo : $(DEPS) inssa.v imperative.vo vminus.vo
	$(COQC) $(COQARG) inssa.v

motion.vo : $(DEPS) motion.v vminus.vo removal.vo insert.vo renaming.vo \
	vsubst.vo
	$(COQC) $(COQARG) motion.v

vsubst.vo : $(DEPS) vsubst.v vminus.vo subst.vo
	$(COQC) $(COQARG) vsubst.v

subst.vo : $(DEPS) subst.v vminus.vo
	$(COQC) $(COQARG) subst.v

removal.vo : $(DEPS) removal.v vminus.vo
	$(COQC) $(COQARG) removal.v

insert.vo : $(DEPS) insert.v removal.vo
	$(COQC) $(COQARG) insert.v

renaming.vo : $(DEPS) renaming.v vminus.vo
	$(COQC) $(COQARG) renaming.v

syntax.vo : $(DEPS) syntax.v
	$(COQC) $(COQARG) syntax.v

syntax.v : syntax.ott $(DEPS)
	$(OTT) -coq_expand_list_types true -i syntax.ott -o syntax.v
	$(VELLVM)/fixott.py syntax.v

infrastructure.ott : infrastructure_aux.vo syntax.ott
	$(VELLVM)/coq2ott.py
	cp merge.ott infrastructure.ott       

m_typings.ott : typings.ott $(VELLVM)/spanlines.py
	$(VELLVM)/spanlines.py typings.ott

infrastructure.v typings.v imperative.v: syntax.ott infrastructure_aux.vo \
	infrastructure.ott m_typings.ott imperative.ott $(DEPS)
	$(OTT) -merge false -coq_expand_list_types true \
            -i syntax.ott -o _tmp_syntax.v \
	    -i infrastructure.ott -o infrastructure.v \
	    -i m_typings.ott -o typings.v \
	    -i imperative.ott -o imperative.v
	rm _tmp_syntax.v
	$(VELLVM)/fixott.py infrastructure.v
	$(VELLVM)/fixott.py typings.v

infrastructure.vo: infrastructure.v $(DEPS)
	$(COQC) $(COQARG) infrastructure.v

typings.vo: typings.v infrastructure.vo analysis.vo
	$(COQC) $(COQARG) typings.v

imperative.vo: imperative.v infrastructure.vo
	$(COQC) $(COQARG) imperative.v

analysis.vo: $(VELLVM)/compcert/Kildall.vo analysis.v $(DEPS) \
	infrastructure.vo infrastructure_props.vo
	$(COQC) $(COQARG) analysis.v

genericvalues.vo: syntax.vo infrastructure.vo genericvalues.v $(DEPS)
	$(COQC) $(COQARG) genericvalues.v

interpreter.vo: interpreter.v syntax.vo infrastructure.vo $(DEPS) \
	genericvalues.vo infrastructure_props.vo opsem.vo
	$(COQC) $(COQARG) interpreter.v

infrastructure_props.vo: infrastructure_props.v syntax.vo infrastructure.vo \
	$(DEPS)
	$(COQC) $(COQARG) infrastructure_props.v

typings_props.vo: typings_props.v syntax.vo infrastructure.vo genericvalues.vo \
	$(DEPS) infrastructure_props.vo typings.vo
	$(COQC) $(COQARG) typings_props.v

opsem.vo: opsem.v typings_props.vo syntax.vo infrastructure.vo \
	genericvalues.vo infrastructure_props.vo
	$(COQC) $(COQARG) opsem.v

opsem_props.vo: opsem_props.v opsem.vo syntax.vo infrastructure.vo \
	genericvalues.vo infrastructure_props.vo
	$(COQC) $(COQARG) opsem_props.v

opsem_wf.vo: opsem_wf.v opsem_props.vo opsem.vo syntax.vo infrastructure.vo\
       genericvalues.vo infrastructure_props.vo $(DEPS)
	$(COQC) $(COQARG) opsem_wf.v

def.tex: syntax.ott infrastructure.ott m_typings.ott main.tex 
	$(OTT) -merge false -o def.tex \
          -tex_show_meta false \
          -tex_wrap false \
            syntax.ott infrastructure.ott m_typings.ott

vminus.vo : vminus.v syntax.vo infrastructure_props.vo typings_props.vo \
	opsem_wf.vo
	$(COQC) $(COQARG) vminus.v

main.pdf: def.tex main.tex
	pdflatex main.tex
	pdflatex main.tex

clean: 
	rm -rf main.pdf main.log main.aux main.log syntax.v infrastructure.v \
		typings.vo *.vo *.glob merge.ott m_*.ott

