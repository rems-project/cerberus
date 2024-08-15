## Grammar
```
<prim_expr> ::= CN_NULL
              | CN_TRUE
              | CN_FALSE
              | CONSTANT
              | CN_CONSTANT
              | <cn_variable>
              | RETURN
              | <prim_expr> DOT <cn_variable>
              | LPAREN <expr> RPAREN
              | CN_ARRAY_SHIFT LT <ctype> GT LPAREN <expr> COMMA <expr>
                RPAREN
              | CN_ARRAY_SHIFT LPAREN <expr> COMMA <expr> RPAREN
              | CN_MEMBER_SHIFT LPAREN <expr> COMMA <cn_variable> RPAREN
              | CN_MEMBER_SHIFT LT <cn_variable> GT LPAREN <expr> COMMA
                <cn_variable> RPAREN
              | <cn_variable> LPAREN [<expr> (COMMA <expr>)*] RPAREN
              | <cn_good> LPAREN <expr> RPAREN
              | <cn_variable> <cons_args>
              | <prim_expr> LBRACK <expr> RBRACK
              | LBRACE <expr> RBRACE PERCENT <NAME> VARIABLE
              | LBRACE <record_def> RBRACE
              | LBRACE <nonempty_member_updates> RBRACE
              | <prim_expr> LBRACK <index_update> (COMMA <index_update>)*
                RBRACK

<unary_expr> ::= <prim_expr>
               | STAR <unary_expr>
               | SIZEOF LT <ctype> GT
               | OFFSETOF LPAREN <cn_variable> COMMA <cn_variable> RPAREN
               | LBRACE <expr> RBRACE CN_UNCHANGED
               | MINUS <unary_expr>
               | BANG <unary_expr>
               | DEFAULT LT <base_type> GT
               | AMPERSAND LPAREN <prim_expr> MINUS_GT <cn_variable> RPAREN
               | AMPERSAND <cn_variable>
               | LPAREN <base_type_explicit> RPAREN <unary_expr>

<mul_expr> ::= <unary_expr>
             | <mul_expr> STAR <unary_expr>
             | <mul_expr> SLASH <unary_expr>

<add_expr> ::= <mul_expr>
             | <add_expr> PLUS <mul_expr>
             | <add_expr> MINUS <mul_expr>

<rel_expr> ::= <add_expr>
             | <rel_expr> EQ_EQ <add_expr>
             | <rel_expr> BANG_EQ <add_expr>
             | <rel_expr> LT <add_expr>
             | <rel_expr> GT <add_expr>
             | <rel_expr> LT_EQ <add_expr>
             | <rel_expr> GT_EQ <add_expr>

<bool_and_expr> ::= <rel_expr> (AMPERSAND_AMPERSAND <rel_expr>)*

<bool_implies_expr> ::= <bool_and_expr> (CN_IMPLIES <bool_and_expr>)*

<bool_or_expr> ::= <bool_implies_expr> (PIPE_PIPE <bool_implies_expr>)*

<list_expr> ::= <bool_or_expr>
              | LBRACK <rel_expr> (COMMA <rel_expr>)* RBRACK

<int_range> ::= CONSTANT COMMA CONSTANT

<member_def> ::= <cn_variable> COLON <expr>

<member_updates> ::= <member_def> COMMA <member_updates>
                   | DOT DOT <expr>

<nonempty_member_updates> ::= <member_def> COMMA <member_updates>

<index_update> ::= <prim_expr> COLON <expr>

<match_cases> ::= <match_case>+

<pattern_member_def> ::= <cn_variable> COLON <pattern>

<pattern_cons_args> ::= LBRACE [<pattern_member_def> (COMMA
                        <pattern_member_def>)*] RBRACE

<pattern> ::= CN_WILD
            | <cn_variable>
            | <cn_variable> <pattern_cons_args>

<match_case> ::= <pattern> EQ GT LBRACE <expr> RBRACE

<match_target> ::= <cn_variable>
                 | LPAREN <expr> RPAREN

<expr_without_let> ::= <list_expr>
                     | <list_expr> QUESTION <list_expr> COLON <list_expr>
                     | IF LPAREN <expr> RPAREN LBRACE <expr> RBRACE ELSE
                       LBRACE <expr> RBRACE
                     | CN_EACH LPAREN <base_type> <cn_variable> COLON
                       <int_range> SEMICOLON <expr> RPAREN
                     | CN_MATCH <match_target> LBRACE <match_cases> RBRACE

<expr> ::= <expr_without_let>
         | CN_LET <cn_variable> EQ <expr> SEMICOLON <expr>

<base_type_explicit> ::= VOID
                       | CN_BOOL
                       | CN_INTEGER
                       | CN_BITS
                       | CN_REAL
                       | CN_POINTER
                       | CN_ALLOC_ID
                       | LBRACE <nonempty_cn_params> RBRACE
                       | STRUCT <cn_variable>
                       | CN_DATATYPE <cn_variable>
                       | CN_LIST LT <base_type> GT
                       | CN_MAP LT <base_type> COMMA <base_type> GT
                       | CN_TUPLE LT [<base_type> (COMMA <base_type>)*] GT
                       | CN_SET LT <base_type> GT

<base_type> ::= <base_type_explicit>
              | <cn_variable>

<cn_good> ::= CN_GOOD LT <ctype> GT

<cn_option_pred_clauses> ::= [LBRACE <clauses> RBRACE]

<cn_cons_case> ::= <cn_variable> LBRACE <cn_args> RBRACE

<cn_cons_cases> ::= [<cn_cons_case> (COMMA <cn_cons_case>)*]

<cn_attrs> ::= [LBRACK [<cn_variable> (COMMA <cn_variable>)*] RBRACK]

<cn_function> ::= CN_FUNCTION <cn_attrs> LPAREN <base_type> RPAREN
                  <cn_variable> LPAREN <cn_args> RPAREN <cn_option_func_body>

<cn_predicate> ::= CN_PREDICATE <cn_attrs> <cn_pred_output> UNAME VARIABLE
                   LPAREN <cn_args> RPAREN <cn_option_pred_clauses>

<cn_lemma> ::= CN_LEMMA <cn_variable> LPAREN <cn_args> RPAREN CN_REQUIRES
               <condition>+ CN_ENSURES <condition>+

<cn_datatype> ::= CN_DATATYPE <cn_variable> LBRACE <cn_cons_cases> RBRACE

<cn_fun_spec> ::= CN_SPEC <cn_variable> LPAREN <cn_args> RPAREN SEMICOLON
                  CN_REQUIRES <condition>+ CN_ENSURES <condition>+

<cn_type_synonym> ::= CN_TYPE_SYNONYM <cn_variable> EQ
                      <opt_paren(<base_type>)>

<cn_variable> ::= <NAME> VARIABLE
                | <NAME> TYPE

<base_type_cn_variable> ::= <base_type> <cn_variable>

<cn_args> ::= [<base_type_cn_variable> (COMMA <base_type_cn_variable>)*]

<nonempty_cn_params> ::= <base_type_cn_variable> (COMMA
                         <base_type_cn_variable>)*

<opt_paren(A)> ::= A
                 | LPAREN A RPAREN

<cn_pred_output> ::= <opt_paren(<base_type>)>

<record_def> ::= <member_def> (COMMA <member_def>)*

<cons_args> ::= LBRACE [<member_def> (COMMA <member_def>)*] RBRACE

<clauses> ::= <clause> SEMICOLON
            | IF LPAREN <expr> RPAREN LBRACE <clause> SEMICOLON RBRACE ELSE
              LBRACE <clauses> RBRACE

<cn_option_func_body> ::= [LBRACE <expr> RBRACE]

<clause> ::= CN_TAKE <cn_variable> EQ <resource> SEMICOLON <clause>
           | CN_LET <cn_variable> EQ <expr> SEMICOLON <clause>
           | ASSERT LPAREN <assert_expr> RPAREN SEMICOLON <clause>
           | RETURN <expr>
           | RETURN

<assert_expr> ::= CN_EACH LPAREN <base_type> <cn_variable> SEMICOLON <expr>
                  RPAREN LBRACE <expr> RBRACE
                | <expr_without_let>

<resource> ::= <pred> LPAREN [<expr> (COMMA <expr>)*] RPAREN
             | CN_EACH LPAREN <base_type> <cn_variable> SEMICOLON <expr>
               RPAREN LBRACE <pred> LPAREN [<expr> (COMMA <expr>)*] RPAREN
               RBRACE

<pred> ::= CN_OWNED LT <ctype> GT
         | CN_OWNED
         | CN_BLOCK LT <ctype> GT
         | UNAME VARIABLE

<ctype> ::= <type_name>

<condition> ::= CN_TAKE <cn_variable> EQ <resource> SEMICOLON
              | CN_LET <cn_variable> EQ <expr> SEMICOLON
              | <assert_expr> SEMICOLON

<function_spec_item> ::= CN_TRUSTED SEMICOLON
                       | CN_ACCESSES (<cn_variable> SEMICOLON)+
                       | CN_REQUIRES <condition>+
                       | CN_ENSURES <condition>+
                       | CN_FUNCTION <cn_variable> SEMICOLON

<function_spec> ::= <function_spec_item>* EOF

<loop_spec> ::= CN_INV <condition>+ EOF

<to_be_instantiated> ::= epsilon
                       | <cn_variable> COMMA
                       | <cn_good> COMMA

<to_be_extracted> ::= [<pred> COMMA]

<cn_statement> ::= CN_PACK <pred> LPAREN [<expr> (COMMA <expr>)*] RPAREN
                   SEMICOLON
                 | CN_UNPACK <pred> LPAREN [<expr> (COMMA <expr>)*] RPAREN
                   SEMICOLON
                 | CN_HAVE <assert_expr> SEMICOLON
                 | CN_EXTRACT <to_be_extracted> <expr> SEMICOLON
                 | CN_INSTANTIATE <to_be_instantiated> <expr> SEMICOLON
                 | CN_SPLIT_CASE <assert_expr> SEMICOLON
                 | CN_UNFOLD <cn_variable> LPAREN [<expr> (COMMA <expr>)*]
                   RPAREN SEMICOLON
                 | CN_APPLY <cn_variable> LPAREN [<expr> (COMMA <expr>)*]
                   RPAREN SEMICOLON
                 | ASSERT LPAREN <assert_expr> RPAREN SEMICOLON
                 | INLINE [<cn_variable> (COMMA <cn_variable>)*] SEMICOLON
                 | CN_PRINT LPAREN <expr> RPAREN SEMICOLON

<cn_statements> ::= <cn_statement>+ EOF

<cn_toplevel_elem> ::= <cn_predicate>
                     | <cn_function>
                     | <cn_lemma>
                     | <cn_datatype>
                     | <cn_type_synonym>
                     | <cn_fun_spec>

<cn_toplevel> ::= <cn_toplevel_elem>* EOF


```
