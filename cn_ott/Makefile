all:
	ott -o mucore.ml mucore.ott
	ott -tex_show_categories true \
	    -tex_suppress_category X \
	    -tex_suppress_ntr annots \
	    -tex_suppress_ntr ty_loc \
	    -tex_suppress_ntr tyvar_TY \
	    -tex_suppress_ntr mu_pval_aux \
	    -tex_suppress_ntr mu_pexpr_aux \
	    -tex_suppress_ntr mu_tpval_aux \
	    -tex_suppress_ntr mu_pattern_aux \
	    -tex_suppress_ntr mu_tpexpr_aux \
	    -tex_suppress_ntr mu_action_aux \
	    -tex_suppress_ntr mu_tval_aux \
	    -tex_suppress_ntr mu_seq_expr_aux \
	    -tex_suppress_ntr mu_seq_expr_aux \
	    -tex_suppress_ntr mu_is_expr_aux \
	    -tex_suppress_ntr mu_seq_texpr_aux \
	    -tex_suppress_ntr mu_is_texpr_aux \
	    -tex_suppress_ntr term_aux \
	    -tex_suppress_ntr tyvar_sym \
	    -tex_suppress_ntr Symbol_sym \
	    -tex_suppress_ntr Symbol_prefix \
	    -tex_suppress_ntr T_ct \
	    -tex_suppress_ntr T_bt \
	    -tex_suppress_ntr ty_act \
	    -tex_suppress_ntr BT_t \
	    -tex_suppress_ntr ty_bt \
	    -tex_suppress_ntr IT_t \
	    -tex_suppress_ntr IT_ts \
	    -o mucore.tex \
	    mucore.ott
	pdflatex mucore.tex

clean:
	rm -rf *~
	rm -rf mucore.aux
	rm -rf mucore-inc.tex
	rm -rf mucore.lem
	rm -rf mucore.log
	rm -rf mucore.pdf
	rm -rf mucore.tex
