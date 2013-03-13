open Alphabet
open BinNat
open BinPos
open Cabs0
open Datatypes
open Int0
open List0
open Validator_main
open Peano
open Specif
open Streams
open Tuples

type __ = Obj.t

module Gram : 
 sig 
  type terminal' =
  | ADD_ASSIGN_t
  | AND_t
  | ANDAND_t
  | AND_ASSIGN_t
  | AUTO_t
  | BANG_t
  | BAR_t
  | BARBAR_t
  | BOOL_t
  | BREAK_t
  | BUILTIN_VA_ARG_t
  | CASE_t
  | CHAR_t
  | COLON_t
  | COMMA_t
  | CONST_t
  | CONSTANT_t
  | CONTINUE_t
  | DEC_t
  | DEFAULT_t
  | DIV_ASSIGN_t
  | DO_t
  | DOT_t
  | DOUBLE_t
  | ELLIPSIS_t
  | ELSE_t
  | ENUM_t
  | EOF_t
  | EQ_t
  | EQEQ_t
  | EXTERN_t
  | FLOAT_t
  | FOR_t
  | GEQ_t
  | GOTO_t
  | GT_t
  | HAT_t
  | IF_t
  | INC_t
  | INLINE_t
  | INT_t
  | LBRACE_t
  | LBRACK_t
  | LEFT_t
  | LEFT_ASSIGN_t
  | LEQ_t
  | LONG_t
  | LPAREN_t
  | LT_t
  | MINUS_t
  | MOD_ASSIGN_t
  | MUL_ASSIGN_t
  | NEQ_t
  | OR_ASSIGN_t
  | OTHER_NAME_t
  | PERCENT_t
  | PLUS_t
  | PTR_t
  | QUESTION_t
  | RBRACE_t
  | RBRACK_t
  | REGISTER_t
  | RESTRICT_t
  | RETURN_t
  | RIGHT_t
  | RIGHT_ASSIGN_t
  | RPAREN_t
  | SEMICOLON_t
  | SHORT_t
  | SIGNED_t
  | SIZEOF_t
  | SLASH_t
  | STAR_t
  | STATIC_t
  | STRUCT_t
  | SUB_ASSIGN_t
  | SWITCH_t
  | TILDE_t
  | TYPEDEF_t
  | TYPEDEF_NAME_t
  | UNION_t
  | UNSIGNED_t
  | VAR_NAME_t
  | VOID_t
  | VOLATILE_t
  | WHILE_t
  | XOR_ASSIGN_t
  
  val terminal'_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> terminal' -> 'a1
  
  val terminal'_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> terminal' -> 'a1
  
  type terminal = terminal'
  
  val terminalNum : terminal coq_Numbered
  
  val coq_TerminalAlph : terminal coq_Alphabet
  
  type nonterminal' =
  | AND_expression_nt
  | Coq_abstract_declarator_nt
  | Coq_additive_expression_nt
  | Coq_argument_expression_list_nt
  | Coq_assignment_expression_nt
  | Coq_assignment_operator_nt
  | Coq_block_item_nt
  | Coq_block_item_list_nt
  | Coq_c_initializer_nt
  | Coq_cast_expression_nt
  | Coq_compound_statement_nt
  | Coq_conditional_expression_nt
  | Coq_constant_expression_nt
  | Coq_declaration_nt
  | Coq_declaration_specifiers_nt
  | Coq_declarator_nt
  | Coq_designation_nt
  | Coq_designator_nt
  | Coq_designator_list_nt
  | Coq_direct_abstract_declarator_nt
  | Coq_direct_declarator_nt
  | Coq_enum_specifier_nt
  | Coq_enumeration_constant_nt
  | Coq_enumerator_nt
  | Coq_enumerator_list_nt
  | Coq_equality_expression_nt
  | Coq_exclusive_OR_expression_nt
  | Coq_expression_nt
  | Coq_expression_statement_nt
  | Coq_external_declaration_nt
  | Coq_function_definition_nt
  | Coq_function_specifier_nt
  | Coq_inclusive_OR_expression_nt
  | Coq_init_declarator_nt
  | Coq_init_declarator_list_nt
  | Coq_initializer_list_nt
  | Coq_iteration_statement_statement_dangerous__nt
  | Coq_iteration_statement_statement_safe__nt
  | Coq_jump_statement_nt
  | Coq_labeled_statement_statement_dangerous__nt
  | Coq_labeled_statement_statement_safe__nt
  | Coq_logical_AND_expression_nt
  | Coq_logical_OR_expression_nt
  | Coq_multiplicative_expression_nt
  | Coq_parameter_declaration_nt
  | Coq_parameter_list_nt
  | Coq_parameter_type_list_nt
  | Coq_pointer_nt
  | Coq_postfix_expression_nt
  | Coq_primary_expression_nt
  | Coq_relational_expression_nt
  | Coq_selection_statement_dangerous_nt
  | Coq_selection_statement_safe_nt
  | Coq_shift_expression_nt
  | Coq_specifier_qualifier_list_nt
  | Coq_statement_dangerous_nt
  | Coq_statement_safe_nt
  | Coq_storage_class_specifier_nt
  | Coq_struct_declaration_nt
  | Coq_struct_declaration_list_nt
  | Coq_struct_declarator_nt
  | Coq_struct_declarator_list_nt
  | Coq_struct_or_union_nt
  | Coq_struct_or_union_specifier_nt
  | Coq_translation_unit_nt
  | Coq_translation_unit_file_nt
  | Coq_type_name_nt
  | Coq_type_qualifier_nt
  | Coq_type_qualifier_list_nt
  | Coq_type_specifier_nt
  | Coq_unary_expression_nt
  | Coq_unary_operator_nt
  
  val nonterminal'_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    nonterminal' -> 'a1
  
  val nonterminal'_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    nonterminal' -> 'a1
  
  type nonterminal = nonterminal'
  
  val nonterminalNum : nonterminal coq_Numbered
  
  val coq_NonTerminalAlph : nonterminal coq_Alphabet
  
  type symbol =
  | T of terminal
  | NT of nonterminal
  
  val symbol_rect :
    (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1
  
  val symbol_rec : (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1
  
  val coq_SymbolAlph : symbol coq_Alphabet
  
  type symbol_semantic_type = __
  
  type production' =
  | Prod_263
  | Prod_262
  | Prod_261
  | Prod_260
  | Prod_259
  | Prod_258
  | Prod_257
  | Prod_256
  | Prod_255
  | Prod_254
  | Prod_253
  | Prod_252
  | Prod_251
  | Prod_250
  | Prod_249
  | Prod_248
  | Prod_247
  | Prod_246
  | Prod_245
  | Prod_244
  | Prod_243
  | Prod_242
  | Prod_241
  | Prod_240
  | Prod_239
  | Prod_238
  | Prod_237
  | Prod_236
  | Prod_235
  | Prod_234
  | Prod_233
  | Prod_232
  | Prod_231
  | Prod_230
  | Prod_229
  | Prod_228
  | Prod_227
  | Prod_226
  | Prod_225
  | Prod_224
  | Prod_223
  | Prod_222
  | Prod_221
  | Prod_220
  | Prod_219
  | Prod_218
  | Prod_217
  | Prod_216
  | Prod_215
  | Prod_214
  | Prod_213
  | Prod_212
  | Prod_211
  | Prod_210
  | Prod_209
  | Prod_208
  | Prod_207
  | Prod_206
  | Prod_205
  | Prod_204
  | Prod_203
  | Prod_202
  | Prod_201
  | Prod_200
  | Prod_199
  | Prod_198
  | Prod_197
  | Prod_196
  | Prod_195
  | Prod_194
  | Prod_193
  | Prod_192
  | Prod_191
  | Prod_190
  | Prod_189
  | Prod_188
  | Prod_187
  | Prod_186
  | Prod_185
  | Prod_184
  | Prod_183
  | Prod_182
  | Prod_181
  | Prod_180
  | Prod_179
  | Prod_178
  | Prod_177
  | Prod_176
  | Prod_175
  | Prod_174
  | Prod_173
  | Prod_172
  | Prod_171
  | Prod_170
  | Prod_169
  | Prod_168
  | Prod_167
  | Prod_166
  | Prod_165
  | Prod_164
  | Prod_163
  | Prod_162
  | Prod_161
  | Prod_160
  | Prod_159
  | Prod_158
  | Prod_157
  | Prod_156
  | Prod_155
  | Prod_154
  | Prod_153
  | Prod_152
  | Prod_151
  | Prod_150
  | Prod_149
  | Prod_148
  | Prod_147
  | Prod_146
  | Prod_145
  | Prod_144
  | Prod_143
  | Prod_142
  | Prod_141
  | Prod_140
  | Prod_139
  | Prod_138
  | Prod_137
  | Prod_136
  | Prod_135
  | Prod_134
  | Prod_133
  | Prod_132
  | Prod_131
  | Prod_130
  | Prod_129
  | Prod_128
  | Prod_127
  | Prod_126
  | Prod_125
  | Prod_124
  | Prod_123
  | Prod_122
  | Prod_121
  | Prod_120
  | Prod_119
  | Prod_118
  | Prod_117
  | Prod_116
  | Prod_115
  | Prod_114
  | Prod_113
  | Prod_112
  | Prod_111
  | Prod_110
  | Prod_109
  | Prod_108
  | Prod_107
  | Prod_106
  | Prod_105
  | Prod_104
  | Prod_103
  | Prod_102
  | Prod_101
  | Prod_100
  | Prod_99
  | Prod_98
  | Prod_97
  | Prod_96
  | Prod_95
  | Prod_94
  | Prod_93
  | Prod_92
  | Prod_91
  | Prod_90
  | Prod_89
  | Prod_88
  | Prod_87
  | Prod_86
  | Prod_85
  | Prod_84
  | Prod_83
  | Prod_82
  | Prod_81
  | Prod_80
  | Prod_79
  | Prod_78
  | Prod_77
  | Prod_76
  | Prod_75
  | Prod_74
  | Prod_73
  | Prod_72
  | Prod_71
  | Prod_70
  | Prod_69
  | Prod_68
  | Prod_67
  | Prod_66
  | Prod_65
  | Prod_64
  | Prod_63
  | Prod_62
  | Prod_61
  | Prod_60
  | Prod_59
  | Prod_58
  | Prod_57
  | Prod_56
  | Prod_55
  | Prod_54
  | Prod_53
  | Prod_52
  | Prod_51
  | Prod_50
  | Prod_49
  | Prod_48
  | Prod_47
  | Prod_46
  | Prod_45
  | Prod_44
  | Prod_43
  | Prod_42
  | Prod_41
  | Prod_40
  | Prod_39
  | Prod_38
  | Prod_37
  | Prod_36
  | Prod_35
  | Prod_34
  | Prod_33
  | Prod_32
  | Prod_31
  | Prod_30
  | Prod_29
  | Prod_28
  | Prod_27
  | Prod_26
  | Prod_25
  | Prod_24
  | Prod_23
  | Prod_22
  | Prod_21
  | Prod_20
  | Prod_19
  | Prod_18
  | Prod_17
  | Prod_16
  | Prod_15
  | Prod_14
  | Prod_13
  | Prod_12
  | Prod_11
  | Prod_10
  | Prod_9
  | Prod_8
  | Prod_7
  | Prod_6
  | Prod_5
  | Prod_4
  | Prod_3
  | Prod_2
  | Prod_1
  
  val production'_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> production' -> 'a1
  
  val production'_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> production' -> 'a1
  
  type production = production'
  
  val productionNum : production coq_Numbered
  
  val coq_ProductionAlph : production coq_Alphabet
  
  val prod_contents :
    production -> (nonterminal*symbol list, symbol_semantic_type arrows) sigT
  
  val prod_lhs : production -> nonterminal
  
  val prod_rhs : production -> symbol list
  
  val prod_action : production -> symbol_semantic_type arrows
  
  val start_symbol : symbol
  
  type token = (terminal, symbol_semantic_type) sigT
  
  type parse_tree =
  | Terminal_pt of terminal * symbol_semantic_type
  | Non_terminal_pt of production * token list * tuple * parse_tree_list
  and parse_tree_list =
  | Nil_ptl
  | Cons_ptl of token list * symbol * symbol_semantic_type * parse_tree
     * token list * symbol list * tuple * parse_tree_list
  
  val parse_tree_rect :
    (terminal -> symbol_semantic_type -> 'a1) -> (production -> token list ->
    tuple -> parse_tree_list -> 'a1) -> symbol -> token list ->
    symbol_semantic_type -> parse_tree -> 'a1
  
  val parse_tree_rec :
    (terminal -> symbol_semantic_type -> 'a1) -> (production -> token list ->
    tuple -> parse_tree_list -> 'a1) -> symbol -> token list ->
    symbol_semantic_type -> parse_tree -> 'a1
  
  val parse_tree_list_rect :
    'a1 -> (token list -> symbol -> symbol_semantic_type -> parse_tree ->
    token list -> symbol list -> tuple -> parse_tree_list -> 'a1 -> 'a1) ->
    symbol list -> token list -> tuple -> parse_tree_list -> 'a1
  
  val parse_tree_list_rec :
    'a1 -> (token list -> symbol -> symbol_semantic_type -> parse_tree ->
    token list -> symbol list -> tuple -> parse_tree_list -> 'a1 -> 'a1) ->
    symbol list -> token list -> tuple -> parse_tree_list -> 'a1
  
  val parse_tree_size :
    symbol -> token list -> symbol_semantic_type -> parse_tree -> nat
  
  val parse_tree_list_size :
    symbol list -> token list -> tuple -> parse_tree_list -> nat
 end
module Coq__1 : 
 sig 
  type terminal' =
  | ADD_ASSIGN_t
  | AND_t
  | ANDAND_t
  | AND_ASSIGN_t
  | AUTO_t
  | BANG_t
  | BAR_t
  | BARBAR_t
  | BOOL_t
  | BREAK_t
  | BUILTIN_VA_ARG_t
  | CASE_t
  | CHAR_t
  | COLON_t
  | COMMA_t
  | CONST_t
  | CONSTANT_t
  | CONTINUE_t
  | DEC_t
  | DEFAULT_t
  | DIV_ASSIGN_t
  | DO_t
  | DOT_t
  | DOUBLE_t
  | ELLIPSIS_t
  | ELSE_t
  | ENUM_t
  | EOF_t
  | EQ_t
  | EQEQ_t
  | EXTERN_t
  | FLOAT_t
  | FOR_t
  | GEQ_t
  | GOTO_t
  | GT_t
  | HAT_t
  | IF_t
  | INC_t
  | INLINE_t
  | INT_t
  | LBRACE_t
  | LBRACK_t
  | LEFT_t
  | LEFT_ASSIGN_t
  | LEQ_t
  | LONG_t
  | LPAREN_t
  | LT_t
  | MINUS_t
  | MOD_ASSIGN_t
  | MUL_ASSIGN_t
  | NEQ_t
  | OR_ASSIGN_t
  | OTHER_NAME_t
  | PERCENT_t
  | PLUS_t
  | PTR_t
  | QUESTION_t
  | RBRACE_t
  | RBRACK_t
  | REGISTER_t
  | RESTRICT_t
  | RETURN_t
  | RIGHT_t
  | RIGHT_ASSIGN_t
  | RPAREN_t
  | SEMICOLON_t
  | SHORT_t
  | SIGNED_t
  | SIZEOF_t
  | SLASH_t
  | STAR_t
  | STATIC_t
  | STRUCT_t
  | SUB_ASSIGN_t
  | SWITCH_t
  | TILDE_t
  | TYPEDEF_t
  | TYPEDEF_NAME_t
  | UNION_t
  | UNSIGNED_t
  | VAR_NAME_t
  | VOID_t
  | VOLATILE_t
  | WHILE_t
  | XOR_ASSIGN_t
  
  val terminal'_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> terminal' -> 'a1
  
  val terminal'_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> terminal' -> 'a1
  
  type terminal = terminal'
  
  val terminalNum : terminal coq_Numbered
  
  val coq_TerminalAlph : terminal coq_Alphabet
  
  type nonterminal' =
  | AND_expression_nt
  | Coq_abstract_declarator_nt
  | Coq_additive_expression_nt
  | Coq_argument_expression_list_nt
  | Coq_assignment_expression_nt
  | Coq_assignment_operator_nt
  | Coq_block_item_nt
  | Coq_block_item_list_nt
  | Coq_c_initializer_nt
  | Coq_cast_expression_nt
  | Coq_compound_statement_nt
  | Coq_conditional_expression_nt
  | Coq_constant_expression_nt
  | Coq_declaration_nt
  | Coq_declaration_specifiers_nt
  | Coq_declarator_nt
  | Coq_designation_nt
  | Coq_designator_nt
  | Coq_designator_list_nt
  | Coq_direct_abstract_declarator_nt
  | Coq_direct_declarator_nt
  | Coq_enum_specifier_nt
  | Coq_enumeration_constant_nt
  | Coq_enumerator_nt
  | Coq_enumerator_list_nt
  | Coq_equality_expression_nt
  | Coq_exclusive_OR_expression_nt
  | Coq_expression_nt
  | Coq_expression_statement_nt
  | Coq_external_declaration_nt
  | Coq_function_definition_nt
  | Coq_function_specifier_nt
  | Coq_inclusive_OR_expression_nt
  | Coq_init_declarator_nt
  | Coq_init_declarator_list_nt
  | Coq_initializer_list_nt
  | Coq_iteration_statement_statement_dangerous__nt
  | Coq_iteration_statement_statement_safe__nt
  | Coq_jump_statement_nt
  | Coq_labeled_statement_statement_dangerous__nt
  | Coq_labeled_statement_statement_safe__nt
  | Coq_logical_AND_expression_nt
  | Coq_logical_OR_expression_nt
  | Coq_multiplicative_expression_nt
  | Coq_parameter_declaration_nt
  | Coq_parameter_list_nt
  | Coq_parameter_type_list_nt
  | Coq_pointer_nt
  | Coq_postfix_expression_nt
  | Coq_primary_expression_nt
  | Coq_relational_expression_nt
  | Coq_selection_statement_dangerous_nt
  | Coq_selection_statement_safe_nt
  | Coq_shift_expression_nt
  | Coq_specifier_qualifier_list_nt
  | Coq_statement_dangerous_nt
  | Coq_statement_safe_nt
  | Coq_storage_class_specifier_nt
  | Coq_struct_declaration_nt
  | Coq_struct_declaration_list_nt
  | Coq_struct_declarator_nt
  | Coq_struct_declarator_list_nt
  | Coq_struct_or_union_nt
  | Coq_struct_or_union_specifier_nt
  | Coq_translation_unit_nt
  | Coq_translation_unit_file_nt
  | Coq_type_name_nt
  | Coq_type_qualifier_nt
  | Coq_type_qualifier_list_nt
  | Coq_type_specifier_nt
  | Coq_unary_expression_nt
  | Coq_unary_operator_nt
  
  val nonterminal'_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    nonterminal' -> 'a1
  
  val nonterminal'_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    nonterminal' -> 'a1
  
  type nonterminal = nonterminal'
  
  val nonterminalNum : nonterminal coq_Numbered
  
  val coq_NonTerminalAlph : nonterminal coq_Alphabet
  
  type symbol =
  | T of terminal
  | NT of nonterminal
  
  val symbol_rect :
    (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1
  
  val symbol_rec : (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1
  
  val coq_SymbolAlph : symbol coq_Alphabet
  
  type symbol_semantic_type = __
  
  type production' =
  | Prod_263
  | Prod_262
  | Prod_261
  | Prod_260
  | Prod_259
  | Prod_258
  | Prod_257
  | Prod_256
  | Prod_255
  | Prod_254
  | Prod_253
  | Prod_252
  | Prod_251
  | Prod_250
  | Prod_249
  | Prod_248
  | Prod_247
  | Prod_246
  | Prod_245
  | Prod_244
  | Prod_243
  | Prod_242
  | Prod_241
  | Prod_240
  | Prod_239
  | Prod_238
  | Prod_237
  | Prod_236
  | Prod_235
  | Prod_234
  | Prod_233
  | Prod_232
  | Prod_231
  | Prod_230
  | Prod_229
  | Prod_228
  | Prod_227
  | Prod_226
  | Prod_225
  | Prod_224
  | Prod_223
  | Prod_222
  | Prod_221
  | Prod_220
  | Prod_219
  | Prod_218
  | Prod_217
  | Prod_216
  | Prod_215
  | Prod_214
  | Prod_213
  | Prod_212
  | Prod_211
  | Prod_210
  | Prod_209
  | Prod_208
  | Prod_207
  | Prod_206
  | Prod_205
  | Prod_204
  | Prod_203
  | Prod_202
  | Prod_201
  | Prod_200
  | Prod_199
  | Prod_198
  | Prod_197
  | Prod_196
  | Prod_195
  | Prod_194
  | Prod_193
  | Prod_192
  | Prod_191
  | Prod_190
  | Prod_189
  | Prod_188
  | Prod_187
  | Prod_186
  | Prod_185
  | Prod_184
  | Prod_183
  | Prod_182
  | Prod_181
  | Prod_180
  | Prod_179
  | Prod_178
  | Prod_177
  | Prod_176
  | Prod_175
  | Prod_174
  | Prod_173
  | Prod_172
  | Prod_171
  | Prod_170
  | Prod_169
  | Prod_168
  | Prod_167
  | Prod_166
  | Prod_165
  | Prod_164
  | Prod_163
  | Prod_162
  | Prod_161
  | Prod_160
  | Prod_159
  | Prod_158
  | Prod_157
  | Prod_156
  | Prod_155
  | Prod_154
  | Prod_153
  | Prod_152
  | Prod_151
  | Prod_150
  | Prod_149
  | Prod_148
  | Prod_147
  | Prod_146
  | Prod_145
  | Prod_144
  | Prod_143
  | Prod_142
  | Prod_141
  | Prod_140
  | Prod_139
  | Prod_138
  | Prod_137
  | Prod_136
  | Prod_135
  | Prod_134
  | Prod_133
  | Prod_132
  | Prod_131
  | Prod_130
  | Prod_129
  | Prod_128
  | Prod_127
  | Prod_126
  | Prod_125
  | Prod_124
  | Prod_123
  | Prod_122
  | Prod_121
  | Prod_120
  | Prod_119
  | Prod_118
  | Prod_117
  | Prod_116
  | Prod_115
  | Prod_114
  | Prod_113
  | Prod_112
  | Prod_111
  | Prod_110
  | Prod_109
  | Prod_108
  | Prod_107
  | Prod_106
  | Prod_105
  | Prod_104
  | Prod_103
  | Prod_102
  | Prod_101
  | Prod_100
  | Prod_99
  | Prod_98
  | Prod_97
  | Prod_96
  | Prod_95
  | Prod_94
  | Prod_93
  | Prod_92
  | Prod_91
  | Prod_90
  | Prod_89
  | Prod_88
  | Prod_87
  | Prod_86
  | Prod_85
  | Prod_84
  | Prod_83
  | Prod_82
  | Prod_81
  | Prod_80
  | Prod_79
  | Prod_78
  | Prod_77
  | Prod_76
  | Prod_75
  | Prod_74
  | Prod_73
  | Prod_72
  | Prod_71
  | Prod_70
  | Prod_69
  | Prod_68
  | Prod_67
  | Prod_66
  | Prod_65
  | Prod_64
  | Prod_63
  | Prod_62
  | Prod_61
  | Prod_60
  | Prod_59
  | Prod_58
  | Prod_57
  | Prod_56
  | Prod_55
  | Prod_54
  | Prod_53
  | Prod_52
  | Prod_51
  | Prod_50
  | Prod_49
  | Prod_48
  | Prod_47
  | Prod_46
  | Prod_45
  | Prod_44
  | Prod_43
  | Prod_42
  | Prod_41
  | Prod_40
  | Prod_39
  | Prod_38
  | Prod_37
  | Prod_36
  | Prod_35
  | Prod_34
  | Prod_33
  | Prod_32
  | Prod_31
  | Prod_30
  | Prod_29
  | Prod_28
  | Prod_27
  | Prod_26
  | Prod_25
  | Prod_24
  | Prod_23
  | Prod_22
  | Prod_21
  | Prod_20
  | Prod_19
  | Prod_18
  | Prod_17
  | Prod_16
  | Prod_15
  | Prod_14
  | Prod_13
  | Prod_12
  | Prod_11
  | Prod_10
  | Prod_9
  | Prod_8
  | Prod_7
  | Prod_6
  | Prod_5
  | Prod_4
  | Prod_3
  | Prod_2
  | Prod_1
  
  val production'_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> production' -> 'a1
  
  val production'_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> production' -> 'a1
  
  type production = production'
  
  val productionNum : production coq_Numbered
  
  val coq_ProductionAlph : production coq_Alphabet
  
  val prod_contents :
    production -> (nonterminal*symbol list, symbol_semantic_type arrows) sigT
  
  val prod_lhs : production -> nonterminal
  
  val prod_rhs : production -> symbol list
  
  val prod_action : production -> symbol_semantic_type arrows
  
  val start_symbol : symbol
  
  type token = (terminal, symbol_semantic_type) sigT
  
  type parse_tree =
  | Terminal_pt of terminal * symbol_semantic_type
  | Non_terminal_pt of production * token list * tuple * parse_tree_list
  and parse_tree_list =
  | Nil_ptl
  | Cons_ptl of token list * symbol * symbol_semantic_type * parse_tree
     * token list * symbol list * tuple * parse_tree_list
  
  val parse_tree_rect :
    (terminal -> symbol_semantic_type -> 'a1) -> (production -> token list ->
    tuple -> parse_tree_list -> 'a1) -> symbol -> token list ->
    symbol_semantic_type -> parse_tree -> 'a1
  
  val parse_tree_rec :
    (terminal -> symbol_semantic_type -> 'a1) -> (production -> token list ->
    tuple -> parse_tree_list -> 'a1) -> symbol -> token list ->
    symbol_semantic_type -> parse_tree -> 'a1
  
  val parse_tree_list_rect :
    'a1 -> (token list -> symbol -> symbol_semantic_type -> parse_tree ->
    token list -> symbol list -> tuple -> parse_tree_list -> 'a1 -> 'a1) ->
    symbol list -> token list -> tuple -> parse_tree_list -> 'a1
  
  val parse_tree_list_rec :
    'a1 -> (token list -> symbol -> symbol_semantic_type -> parse_tree ->
    token list -> symbol list -> tuple -> parse_tree_list -> 'a1 -> 'a1) ->
    symbol list -> token list -> tuple -> parse_tree_list -> 'a1
  
  val parse_tree_size :
    symbol -> token list -> symbol_semantic_type -> parse_tree -> nat
  
  val parse_tree_list_size :
    symbol list -> token list -> tuple -> parse_tree_list -> nat
 end

module Aut : 
 sig 
  module Gram : 
   sig 
    type terminal' = Gram.terminal' =
    | ADD_ASSIGN_t
    | AND_t
    | ANDAND_t
    | AND_ASSIGN_t
    | AUTO_t
    | BANG_t
    | BAR_t
    | BARBAR_t
    | BOOL_t
    | BREAK_t
    | BUILTIN_VA_ARG_t
    | CASE_t
    | CHAR_t
    | COLON_t
    | COMMA_t
    | CONST_t
    | CONSTANT_t
    | CONTINUE_t
    | DEC_t
    | DEFAULT_t
    | DIV_ASSIGN_t
    | DO_t
    | DOT_t
    | DOUBLE_t
    | ELLIPSIS_t
    | ELSE_t
    | ENUM_t
    | EOF_t
    | EQ_t
    | EQEQ_t
    | EXTERN_t
    | FLOAT_t
    | FOR_t
    | GEQ_t
    | GOTO_t
    | GT_t
    | HAT_t
    | IF_t
    | INC_t
    | INLINE_t
    | INT_t
    | LBRACE_t
    | LBRACK_t
    | LEFT_t
    | LEFT_ASSIGN_t
    | LEQ_t
    | LONG_t
    | LPAREN_t
    | LT_t
    | MINUS_t
    | MOD_ASSIGN_t
    | MUL_ASSIGN_t
    | NEQ_t
    | OR_ASSIGN_t
    | OTHER_NAME_t
    | PERCENT_t
    | PLUS_t
    | PTR_t
    | QUESTION_t
    | RBRACE_t
    | RBRACK_t
    | REGISTER_t
    | RESTRICT_t
    | RETURN_t
    | RIGHT_t
    | RIGHT_ASSIGN_t
    | RPAREN_t
    | SEMICOLON_t
    | SHORT_t
    | SIGNED_t
    | SIZEOF_t
    | SLASH_t
    | STAR_t
    | STATIC_t
    | STRUCT_t
    | SUB_ASSIGN_t
    | SWITCH_t
    | TILDE_t
    | TYPEDEF_t
    | TYPEDEF_NAME_t
    | UNION_t
    | UNSIGNED_t
    | VAR_NAME_t
    | VOID_t
    | VOLATILE_t
    | WHILE_t
    | XOR_ASSIGN_t
    
    val terminal'_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> terminal' -> 'a1
    
    val terminal'_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> terminal' -> 'a1
    
    type terminal = terminal'
    
    val terminalNum : terminal coq_Numbered
    
    val coq_TerminalAlph : terminal coq_Alphabet
    
    type nonterminal' = Gram.nonterminal' =
    | AND_expression_nt
    | Coq_abstract_declarator_nt
    | Coq_additive_expression_nt
    | Coq_argument_expression_list_nt
    | Coq_assignment_expression_nt
    | Coq_assignment_operator_nt
    | Coq_block_item_nt
    | Coq_block_item_list_nt
    | Coq_c_initializer_nt
    | Coq_cast_expression_nt
    | Coq_compound_statement_nt
    | Coq_conditional_expression_nt
    | Coq_constant_expression_nt
    | Coq_declaration_nt
    | Coq_declaration_specifiers_nt
    | Coq_declarator_nt
    | Coq_designation_nt
    | Coq_designator_nt
    | Coq_designator_list_nt
    | Coq_direct_abstract_declarator_nt
    | Coq_direct_declarator_nt
    | Coq_enum_specifier_nt
    | Coq_enumeration_constant_nt
    | Coq_enumerator_nt
    | Coq_enumerator_list_nt
    | Coq_equality_expression_nt
    | Coq_exclusive_OR_expression_nt
    | Coq_expression_nt
    | Coq_expression_statement_nt
    | Coq_external_declaration_nt
    | Coq_function_definition_nt
    | Coq_function_specifier_nt
    | Coq_inclusive_OR_expression_nt
    | Coq_init_declarator_nt
    | Coq_init_declarator_list_nt
    | Coq_initializer_list_nt
    | Coq_iteration_statement_statement_dangerous__nt
    | Coq_iteration_statement_statement_safe__nt
    | Coq_jump_statement_nt
    | Coq_labeled_statement_statement_dangerous__nt
    | Coq_labeled_statement_statement_safe__nt
    | Coq_logical_AND_expression_nt
    | Coq_logical_OR_expression_nt
    | Coq_multiplicative_expression_nt
    | Coq_parameter_declaration_nt
    | Coq_parameter_list_nt
    | Coq_parameter_type_list_nt
    | Coq_pointer_nt
    | Coq_postfix_expression_nt
    | Coq_primary_expression_nt
    | Coq_relational_expression_nt
    | Coq_selection_statement_dangerous_nt
    | Coq_selection_statement_safe_nt
    | Coq_shift_expression_nt
    | Coq_specifier_qualifier_list_nt
    | Coq_statement_dangerous_nt
    | Coq_statement_safe_nt
    | Coq_storage_class_specifier_nt
    | Coq_struct_declaration_nt
    | Coq_struct_declaration_list_nt
    | Coq_struct_declarator_nt
    | Coq_struct_declarator_list_nt
    | Coq_struct_or_union_nt
    | Coq_struct_or_union_specifier_nt
    | Coq_translation_unit_nt
    | Coq_translation_unit_file_nt
    | Coq_type_name_nt
    | Coq_type_qualifier_nt
    | Coq_type_qualifier_list_nt
    | Coq_type_specifier_nt
    | Coq_unary_expression_nt
    | Coq_unary_operator_nt
    
    val nonterminal'_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> nonterminal' -> 'a1
    
    val nonterminal'_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> nonterminal' -> 'a1
    
    type nonterminal = nonterminal'
    
    val nonterminalNum : nonterminal coq_Numbered
    
    val coq_NonTerminalAlph : nonterminal coq_Alphabet
    
    type symbol = Gram.symbol =
    | T of terminal
    | NT of nonterminal
    
    val symbol_rect :
      (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1
    
    val symbol_rec :
      (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1
    
    val coq_SymbolAlph : symbol coq_Alphabet
    
    type symbol_semantic_type = __
    
    type production' = Gram.production' =
    | Prod_263
    | Prod_262
    | Prod_261
    | Prod_260
    | Prod_259
    | Prod_258
    | Prod_257
    | Prod_256
    | Prod_255
    | Prod_254
    | Prod_253
    | Prod_252
    | Prod_251
    | Prod_250
    | Prod_249
    | Prod_248
    | Prod_247
    | Prod_246
    | Prod_245
    | Prod_244
    | Prod_243
    | Prod_242
    | Prod_241
    | Prod_240
    | Prod_239
    | Prod_238
    | Prod_237
    | Prod_236
    | Prod_235
    | Prod_234
    | Prod_233
    | Prod_232
    | Prod_231
    | Prod_230
    | Prod_229
    | Prod_228
    | Prod_227
    | Prod_226
    | Prod_225
    | Prod_224
    | Prod_223
    | Prod_222
    | Prod_221
    | Prod_220
    | Prod_219
    | Prod_218
    | Prod_217
    | Prod_216
    | Prod_215
    | Prod_214
    | Prod_213
    | Prod_212
    | Prod_211
    | Prod_210
    | Prod_209
    | Prod_208
    | Prod_207
    | Prod_206
    | Prod_205
    | Prod_204
    | Prod_203
    | Prod_202
    | Prod_201
    | Prod_200
    | Prod_199
    | Prod_198
    | Prod_197
    | Prod_196
    | Prod_195
    | Prod_194
    | Prod_193
    | Prod_192
    | Prod_191
    | Prod_190
    | Prod_189
    | Prod_188
    | Prod_187
    | Prod_186
    | Prod_185
    | Prod_184
    | Prod_183
    | Prod_182
    | Prod_181
    | Prod_180
    | Prod_179
    | Prod_178
    | Prod_177
    | Prod_176
    | Prod_175
    | Prod_174
    | Prod_173
    | Prod_172
    | Prod_171
    | Prod_170
    | Prod_169
    | Prod_168
    | Prod_167
    | Prod_166
    | Prod_165
    | Prod_164
    | Prod_163
    | Prod_162
    | Prod_161
    | Prod_160
    | Prod_159
    | Prod_158
    | Prod_157
    | Prod_156
    | Prod_155
    | Prod_154
    | Prod_153
    | Prod_152
    | Prod_151
    | Prod_150
    | Prod_149
    | Prod_148
    | Prod_147
    | Prod_146
    | Prod_145
    | Prod_144
    | Prod_143
    | Prod_142
    | Prod_141
    | Prod_140
    | Prod_139
    | Prod_138
    | Prod_137
    | Prod_136
    | Prod_135
    | Prod_134
    | Prod_133
    | Prod_132
    | Prod_131
    | Prod_130
    | Prod_129
    | Prod_128
    | Prod_127
    | Prod_126
    | Prod_125
    | Prod_124
    | Prod_123
    | Prod_122
    | Prod_121
    | Prod_120
    | Prod_119
    | Prod_118
    | Prod_117
    | Prod_116
    | Prod_115
    | Prod_114
    | Prod_113
    | Prod_112
    | Prod_111
    | Prod_110
    | Prod_109
    | Prod_108
    | Prod_107
    | Prod_106
    | Prod_105
    | Prod_104
    | Prod_103
    | Prod_102
    | Prod_101
    | Prod_100
    | Prod_99
    | Prod_98
    | Prod_97
    | Prod_96
    | Prod_95
    | Prod_94
    | Prod_93
    | Prod_92
    | Prod_91
    | Prod_90
    | Prod_89
    | Prod_88
    | Prod_87
    | Prod_86
    | Prod_85
    | Prod_84
    | Prod_83
    | Prod_82
    | Prod_81
    | Prod_80
    | Prod_79
    | Prod_78
    | Prod_77
    | Prod_76
    | Prod_75
    | Prod_74
    | Prod_73
    | Prod_72
    | Prod_71
    | Prod_70
    | Prod_69
    | Prod_68
    | Prod_67
    | Prod_66
    | Prod_65
    | Prod_64
    | Prod_63
    | Prod_62
    | Prod_61
    | Prod_60
    | Prod_59
    | Prod_58
    | Prod_57
    | Prod_56
    | Prod_55
    | Prod_54
    | Prod_53
    | Prod_52
    | Prod_51
    | Prod_50
    | Prod_49
    | Prod_48
    | Prod_47
    | Prod_46
    | Prod_45
    | Prod_44
    | Prod_43
    | Prod_42
    | Prod_41
    | Prod_40
    | Prod_39
    | Prod_38
    | Prod_37
    | Prod_36
    | Prod_35
    | Prod_34
    | Prod_33
    | Prod_32
    | Prod_31
    | Prod_30
    | Prod_29
    | Prod_28
    | Prod_27
    | Prod_26
    | Prod_25
    | Prod_24
    | Prod_23
    | Prod_22
    | Prod_21
    | Prod_20
    | Prod_19
    | Prod_18
    | Prod_17
    | Prod_16
    | Prod_15
    | Prod_14
    | Prod_13
    | Prod_12
    | Prod_11
    | Prod_10
    | Prod_9
    | Prod_8
    | Prod_7
    | Prod_6
    | Prod_5
    | Prod_4
    | Prod_3
    | Prod_2
    | Prod_1
    
    val production'_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> production' -> 'a1
    
    val production'_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> production' -> 'a1
    
    type production = production'
    
    val productionNum : production coq_Numbered
    
    val coq_ProductionAlph : production coq_Alphabet
    
    val prod_contents :
      production -> (nonterminal*symbol list, symbol_semantic_type arrows)
      sigT
    
    val prod_lhs : production -> nonterminal
    
    val prod_rhs : production -> symbol list
    
    val prod_action : production -> symbol_semantic_type arrows
    
    val start_symbol : symbol
    
    type token = (terminal, symbol_semantic_type) sigT
    
    type parse_tree =
    | Terminal_pt of terminal * symbol_semantic_type
    | Non_terminal_pt of production * token list * tuple * parse_tree_list
    and parse_tree_list =
    | Nil_ptl
    | Cons_ptl of token list * symbol * symbol_semantic_type * parse_tree
       * token list * symbol list * tuple * parse_tree_list
    
    val parse_tree_rect :
      (terminal -> symbol_semantic_type -> 'a1) -> (production -> token list
      -> tuple -> parse_tree_list -> 'a1) -> symbol -> token list ->
      symbol_semantic_type -> parse_tree -> 'a1
    
    val parse_tree_rec :
      (terminal -> symbol_semantic_type -> 'a1) -> (production -> token list
      -> tuple -> parse_tree_list -> 'a1) -> symbol -> token list ->
      symbol_semantic_type -> parse_tree -> 'a1
    
    val parse_tree_list_rect :
      'a1 -> (token list -> symbol -> symbol_semantic_type -> parse_tree ->
      token list -> symbol list -> tuple -> parse_tree_list -> 'a1 -> 'a1) ->
      symbol list -> token list -> tuple -> parse_tree_list -> 'a1
    
    val parse_tree_list_rec :
      'a1 -> (token list -> symbol -> symbol_semantic_type -> parse_tree ->
      token list -> symbol list -> tuple -> parse_tree_list -> 'a1 -> 'a1) ->
      symbol list -> token list -> tuple -> parse_tree_list -> 'a1
    
    val parse_tree_size :
      symbol -> token list -> symbol_semantic_type -> parse_tree -> nat
    
    val parse_tree_list_size :
      symbol list -> token list -> tuple -> parse_tree_list -> nat
   end
  
  module GramDefs : 
   sig 
    type terminal' = Coq__1.terminal' =
    | ADD_ASSIGN_t
    | AND_t
    | ANDAND_t
    | AND_ASSIGN_t
    | AUTO_t
    | BANG_t
    | BAR_t
    | BARBAR_t
    | BOOL_t
    | BREAK_t
    | BUILTIN_VA_ARG_t
    | CASE_t
    | CHAR_t
    | COLON_t
    | COMMA_t
    | CONST_t
    | CONSTANT_t
    | CONTINUE_t
    | DEC_t
    | DEFAULT_t
    | DIV_ASSIGN_t
    | DO_t
    | DOT_t
    | DOUBLE_t
    | ELLIPSIS_t
    | ELSE_t
    | ENUM_t
    | EOF_t
    | EQ_t
    | EQEQ_t
    | EXTERN_t
    | FLOAT_t
    | FOR_t
    | GEQ_t
    | GOTO_t
    | GT_t
    | HAT_t
    | IF_t
    | INC_t
    | INLINE_t
    | INT_t
    | LBRACE_t
    | LBRACK_t
    | LEFT_t
    | LEFT_ASSIGN_t
    | LEQ_t
    | LONG_t
    | LPAREN_t
    | LT_t
    | MINUS_t
    | MOD_ASSIGN_t
    | MUL_ASSIGN_t
    | NEQ_t
    | OR_ASSIGN_t
    | OTHER_NAME_t
    | PERCENT_t
    | PLUS_t
    | PTR_t
    | QUESTION_t
    | RBRACE_t
    | RBRACK_t
    | REGISTER_t
    | RESTRICT_t
    | RETURN_t
    | RIGHT_t
    | RIGHT_ASSIGN_t
    | RPAREN_t
    | SEMICOLON_t
    | SHORT_t
    | SIGNED_t
    | SIZEOF_t
    | SLASH_t
    | STAR_t
    | STATIC_t
    | STRUCT_t
    | SUB_ASSIGN_t
    | SWITCH_t
    | TILDE_t
    | TYPEDEF_t
    | TYPEDEF_NAME_t
    | UNION_t
    | UNSIGNED_t
    | VAR_NAME_t
    | VOID_t
    | VOLATILE_t
    | WHILE_t
    | XOR_ASSIGN_t
    
    val terminal'_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> terminal' -> 'a1
    
    val terminal'_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> terminal' -> 'a1
    
    type terminal = terminal'
    
    val terminalNum : terminal coq_Numbered
    
    val coq_TerminalAlph : terminal coq_Alphabet
    
    type nonterminal' = Coq__1.nonterminal' =
    | AND_expression_nt
    | Coq_abstract_declarator_nt
    | Coq_additive_expression_nt
    | Coq_argument_expression_list_nt
    | Coq_assignment_expression_nt
    | Coq_assignment_operator_nt
    | Coq_block_item_nt
    | Coq_block_item_list_nt
    | Coq_c_initializer_nt
    | Coq_cast_expression_nt
    | Coq_compound_statement_nt
    | Coq_conditional_expression_nt
    | Coq_constant_expression_nt
    | Coq_declaration_nt
    | Coq_declaration_specifiers_nt
    | Coq_declarator_nt
    | Coq_designation_nt
    | Coq_designator_nt
    | Coq_designator_list_nt
    | Coq_direct_abstract_declarator_nt
    | Coq_direct_declarator_nt
    | Coq_enum_specifier_nt
    | Coq_enumeration_constant_nt
    | Coq_enumerator_nt
    | Coq_enumerator_list_nt
    | Coq_equality_expression_nt
    | Coq_exclusive_OR_expression_nt
    | Coq_expression_nt
    | Coq_expression_statement_nt
    | Coq_external_declaration_nt
    | Coq_function_definition_nt
    | Coq_function_specifier_nt
    | Coq_inclusive_OR_expression_nt
    | Coq_init_declarator_nt
    | Coq_init_declarator_list_nt
    | Coq_initializer_list_nt
    | Coq_iteration_statement_statement_dangerous__nt
    | Coq_iteration_statement_statement_safe__nt
    | Coq_jump_statement_nt
    | Coq_labeled_statement_statement_dangerous__nt
    | Coq_labeled_statement_statement_safe__nt
    | Coq_logical_AND_expression_nt
    | Coq_logical_OR_expression_nt
    | Coq_multiplicative_expression_nt
    | Coq_parameter_declaration_nt
    | Coq_parameter_list_nt
    | Coq_parameter_type_list_nt
    | Coq_pointer_nt
    | Coq_postfix_expression_nt
    | Coq_primary_expression_nt
    | Coq_relational_expression_nt
    | Coq_selection_statement_dangerous_nt
    | Coq_selection_statement_safe_nt
    | Coq_shift_expression_nt
    | Coq_specifier_qualifier_list_nt
    | Coq_statement_dangerous_nt
    | Coq_statement_safe_nt
    | Coq_storage_class_specifier_nt
    | Coq_struct_declaration_nt
    | Coq_struct_declaration_list_nt
    | Coq_struct_declarator_nt
    | Coq_struct_declarator_list_nt
    | Coq_struct_or_union_nt
    | Coq_struct_or_union_specifier_nt
    | Coq_translation_unit_nt
    | Coq_translation_unit_file_nt
    | Coq_type_name_nt
    | Coq_type_qualifier_nt
    | Coq_type_qualifier_list_nt
    | Coq_type_specifier_nt
    | Coq_unary_expression_nt
    | Coq_unary_operator_nt
    
    val nonterminal'_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> nonterminal' -> 'a1
    
    val nonterminal'_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> nonterminal' -> 'a1
    
    type nonterminal = nonterminal'
    
    val nonterminalNum : nonterminal coq_Numbered
    
    val coq_NonTerminalAlph : nonterminal coq_Alphabet
    
    type symbol = Coq__1.symbol =
    | T of terminal
    | NT of nonterminal
    
    val symbol_rect :
      (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1
    
    val symbol_rec :
      (terminal -> 'a1) -> (nonterminal -> 'a1) -> symbol -> 'a1
    
    val coq_SymbolAlph : symbol coq_Alphabet
    
    type symbol_semantic_type = __
    
    type production' = Coq__1.production' =
    | Prod_263
    | Prod_262
    | Prod_261
    | Prod_260
    | Prod_259
    | Prod_258
    | Prod_257
    | Prod_256
    | Prod_255
    | Prod_254
    | Prod_253
    | Prod_252
    | Prod_251
    | Prod_250
    | Prod_249
    | Prod_248
    | Prod_247
    | Prod_246
    | Prod_245
    | Prod_244
    | Prod_243
    | Prod_242
    | Prod_241
    | Prod_240
    | Prod_239
    | Prod_238
    | Prod_237
    | Prod_236
    | Prod_235
    | Prod_234
    | Prod_233
    | Prod_232
    | Prod_231
    | Prod_230
    | Prod_229
    | Prod_228
    | Prod_227
    | Prod_226
    | Prod_225
    | Prod_224
    | Prod_223
    | Prod_222
    | Prod_221
    | Prod_220
    | Prod_219
    | Prod_218
    | Prod_217
    | Prod_216
    | Prod_215
    | Prod_214
    | Prod_213
    | Prod_212
    | Prod_211
    | Prod_210
    | Prod_209
    | Prod_208
    | Prod_207
    | Prod_206
    | Prod_205
    | Prod_204
    | Prod_203
    | Prod_202
    | Prod_201
    | Prod_200
    | Prod_199
    | Prod_198
    | Prod_197
    | Prod_196
    | Prod_195
    | Prod_194
    | Prod_193
    | Prod_192
    | Prod_191
    | Prod_190
    | Prod_189
    | Prod_188
    | Prod_187
    | Prod_186
    | Prod_185
    | Prod_184
    | Prod_183
    | Prod_182
    | Prod_181
    | Prod_180
    | Prod_179
    | Prod_178
    | Prod_177
    | Prod_176
    | Prod_175
    | Prod_174
    | Prod_173
    | Prod_172
    | Prod_171
    | Prod_170
    | Prod_169
    | Prod_168
    | Prod_167
    | Prod_166
    | Prod_165
    | Prod_164
    | Prod_163
    | Prod_162
    | Prod_161
    | Prod_160
    | Prod_159
    | Prod_158
    | Prod_157
    | Prod_156
    | Prod_155
    | Prod_154
    | Prod_153
    | Prod_152
    | Prod_151
    | Prod_150
    | Prod_149
    | Prod_148
    | Prod_147
    | Prod_146
    | Prod_145
    | Prod_144
    | Prod_143
    | Prod_142
    | Prod_141
    | Prod_140
    | Prod_139
    | Prod_138
    | Prod_137
    | Prod_136
    | Prod_135
    | Prod_134
    | Prod_133
    | Prod_132
    | Prod_131
    | Prod_130
    | Prod_129
    | Prod_128
    | Prod_127
    | Prod_126
    | Prod_125
    | Prod_124
    | Prod_123
    | Prod_122
    | Prod_121
    | Prod_120
    | Prod_119
    | Prod_118
    | Prod_117
    | Prod_116
    | Prod_115
    | Prod_114
    | Prod_113
    | Prod_112
    | Prod_111
    | Prod_110
    | Prod_109
    | Prod_108
    | Prod_107
    | Prod_106
    | Prod_105
    | Prod_104
    | Prod_103
    | Prod_102
    | Prod_101
    | Prod_100
    | Prod_99
    | Prod_98
    | Prod_97
    | Prod_96
    | Prod_95
    | Prod_94
    | Prod_93
    | Prod_92
    | Prod_91
    | Prod_90
    | Prod_89
    | Prod_88
    | Prod_87
    | Prod_86
    | Prod_85
    | Prod_84
    | Prod_83
    | Prod_82
    | Prod_81
    | Prod_80
    | Prod_79
    | Prod_78
    | Prod_77
    | Prod_76
    | Prod_75
    | Prod_74
    | Prod_73
    | Prod_72
    | Prod_71
    | Prod_70
    | Prod_69
    | Prod_68
    | Prod_67
    | Prod_66
    | Prod_65
    | Prod_64
    | Prod_63
    | Prod_62
    | Prod_61
    | Prod_60
    | Prod_59
    | Prod_58
    | Prod_57
    | Prod_56
    | Prod_55
    | Prod_54
    | Prod_53
    | Prod_52
    | Prod_51
    | Prod_50
    | Prod_49
    | Prod_48
    | Prod_47
    | Prod_46
    | Prod_45
    | Prod_44
    | Prod_43
    | Prod_42
    | Prod_41
    | Prod_40
    | Prod_39
    | Prod_38
    | Prod_37
    | Prod_36
    | Prod_35
    | Prod_34
    | Prod_33
    | Prod_32
    | Prod_31
    | Prod_30
    | Prod_29
    | Prod_28
    | Prod_27
    | Prod_26
    | Prod_25
    | Prod_24
    | Prod_23
    | Prod_22
    | Prod_21
    | Prod_20
    | Prod_19
    | Prod_18
    | Prod_17
    | Prod_16
    | Prod_15
    | Prod_14
    | Prod_13
    | Prod_12
    | Prod_11
    | Prod_10
    | Prod_9
    | Prod_8
    | Prod_7
    | Prod_6
    | Prod_5
    | Prod_4
    | Prod_3
    | Prod_2
    | Prod_1
    
    val production'_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> production' -> 'a1
    
    val production'_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> production' -> 'a1
    
    type production = production'
    
    val productionNum : production coq_Numbered
    
    val coq_ProductionAlph : production coq_Alphabet
    
    val prod_contents :
      production -> (nonterminal*symbol list, symbol_semantic_type arrows)
      sigT
    
    val prod_lhs : production -> nonterminal
    
    val prod_rhs : production -> symbol list
    
    val prod_action : production -> symbol_semantic_type arrows
    
    val start_symbol : symbol
    
    type token = (terminal, symbol_semantic_type) sigT
    
    type parse_tree = Coq__1.parse_tree =
    | Terminal_pt of terminal * symbol_semantic_type
    | Non_terminal_pt of production * token list * tuple * parse_tree_list
    and parse_tree_list = Coq__1.parse_tree_list =
    | Nil_ptl
    | Cons_ptl of token list * symbol * symbol_semantic_type * parse_tree
       * token list * symbol list * tuple * parse_tree_list
    
    val parse_tree_rect :
      (terminal -> symbol_semantic_type -> 'a1) -> (production -> token list
      -> tuple -> parse_tree_list -> 'a1) -> symbol -> token list ->
      symbol_semantic_type -> parse_tree -> 'a1
    
    val parse_tree_rec :
      (terminal -> symbol_semantic_type -> 'a1) -> (production -> token list
      -> tuple -> parse_tree_list -> 'a1) -> symbol -> token list ->
      symbol_semantic_type -> parse_tree -> 'a1
    
    val parse_tree_list_rect :
      'a1 -> (token list -> symbol -> symbol_semantic_type -> parse_tree ->
      token list -> symbol list -> tuple -> parse_tree_list -> 'a1 -> 'a1) ->
      symbol list -> token list -> tuple -> parse_tree_list -> 'a1
    
    val parse_tree_list_rec :
      'a1 -> (token list -> symbol -> symbol_semantic_type -> parse_tree ->
      token list -> symbol list -> tuple -> parse_tree_list -> 'a1 -> 'a1) ->
      symbol list -> token list -> tuple -> parse_tree_list -> 'a1
    
    val parse_tree_size :
      symbol -> token list -> symbol_semantic_type -> parse_tree -> nat
    
    val parse_tree_list_size :
      symbol list -> token list -> tuple -> parse_tree_list -> nat
   end
  
  val nullable_nterm : Coq__1.nonterminal -> bool
  
  val first_nterm : Coq__1.nonterminal -> Coq__1.terminal list
  
  type noninitstate' =
  | Nis_504
  | Nis_503
  | Nis_502
  | Nis_501
  | Nis_500
  | Nis_499
  | Nis_498
  | Nis_497
  | Nis_496
  | Nis_495
  | Nis_494
  | Nis_493
  | Nis_492
  | Nis_491
  | Nis_490
  | Nis_489
  | Nis_488
  | Nis_487
  | Nis_486
  | Nis_485
  | Nis_484
  | Nis_483
  | Nis_482
  | Nis_481
  | Nis_480
  | Nis_479
  | Nis_478
  | Nis_477
  | Nis_476
  | Nis_475
  | Nis_474
  | Nis_473
  | Nis_472
  | Nis_471
  | Nis_470
  | Nis_469
  | Nis_468
  | Nis_467
  | Nis_466
  | Nis_465
  | Nis_464
  | Nis_463
  | Nis_462
  | Nis_461
  | Nis_460
  | Nis_459
  | Nis_458
  | Nis_457
  | Nis_456
  | Nis_455
  | Nis_454
  | Nis_453
  | Nis_452
  | Nis_451
  | Nis_450
  | Nis_449
  | Nis_448
  | Nis_447
  | Nis_446
  | Nis_445
  | Nis_444
  | Nis_443
  | Nis_442
  | Nis_441
  | Nis_440
  | Nis_439
  | Nis_438
  | Nis_437
  | Nis_436
  | Nis_435
  | Nis_434
  | Nis_433
  | Nis_432
  | Nis_431
  | Nis_430
  | Nis_429
  | Nis_428
  | Nis_427
  | Nis_426
  | Nis_425
  | Nis_424
  | Nis_423
  | Nis_422
  | Nis_421
  | Nis_420
  | Nis_419
  | Nis_418
  | Nis_417
  | Nis_416
  | Nis_415
  | Nis_414
  | Nis_413
  | Nis_412
  | Nis_411
  | Nis_410
  | Nis_409
  | Nis_408
  | Nis_407
  | Nis_406
  | Nis_405
  | Nis_404
  | Nis_403
  | Nis_402
  | Nis_401
  | Nis_400
  | Nis_399
  | Nis_398
  | Nis_397
  | Nis_396
  | Nis_395
  | Nis_394
  | Nis_393
  | Nis_392
  | Nis_391
  | Nis_390
  | Nis_389
  | Nis_388
  | Nis_387
  | Nis_386
  | Nis_385
  | Nis_384
  | Nis_383
  | Nis_382
  | Nis_381
  | Nis_380
  | Nis_379
  | Nis_378
  | Nis_377
  | Nis_376
  | Nis_375
  | Nis_374
  | Nis_373
  | Nis_372
  | Nis_371
  | Nis_370
  | Nis_369
  | Nis_368
  | Nis_367
  | Nis_366
  | Nis_365
  | Nis_364
  | Nis_363
  | Nis_362
  | Nis_361
  | Nis_360
  | Nis_359
  | Nis_358
  | Nis_357
  | Nis_356
  | Nis_355
  | Nis_354
  | Nis_353
  | Nis_352
  | Nis_351
  | Nis_350
  | Nis_349
  | Nis_348
  | Nis_347
  | Nis_346
  | Nis_345
  | Nis_344
  | Nis_343
  | Nis_342
  | Nis_341
  | Nis_340
  | Nis_339
  | Nis_338
  | Nis_337
  | Nis_336
  | Nis_335
  | Nis_334
  | Nis_333
  | Nis_332
  | Nis_331
  | Nis_330
  | Nis_329
  | Nis_328
  | Nis_327
  | Nis_326
  | Nis_325
  | Nis_324
  | Nis_323
  | Nis_322
  | Nis_321
  | Nis_320
  | Nis_319
  | Nis_318
  | Nis_317
  | Nis_316
  | Nis_315
  | Nis_314
  | Nis_313
  | Nis_312
  | Nis_311
  | Nis_310
  | Nis_309
  | Nis_308
  | Nis_307
  | Nis_306
  | Nis_305
  | Nis_304
  | Nis_303
  | Nis_302
  | Nis_301
  | Nis_300
  | Nis_299
  | Nis_298
  | Nis_297
  | Nis_296
  | Nis_295
  | Nis_294
  | Nis_293
  | Nis_292
  | Nis_291
  | Nis_290
  | Nis_289
  | Nis_288
  | Nis_287
  | Nis_286
  | Nis_285
  | Nis_284
  | Nis_283
  | Nis_282
  | Nis_281
  | Nis_280
  | Nis_279
  | Nis_278
  | Nis_277
  | Nis_276
  | Nis_275
  | Nis_274
  | Nis_273
  | Nis_272
  | Nis_271
  | Nis_270
  | Nis_269
  | Nis_268
  | Nis_267
  | Nis_266
  | Nis_265
  | Nis_264
  | Nis_263
  | Nis_262
  | Nis_261
  | Nis_260
  | Nis_259
  | Nis_258
  | Nis_257
  | Nis_256
  | Nis_255
  | Nis_254
  | Nis_253
  | Nis_252
  | Nis_251
  | Nis_250
  | Nis_249
  | Nis_248
  | Nis_247
  | Nis_246
  | Nis_245
  | Nis_244
  | Nis_243
  | Nis_242
  | Nis_241
  | Nis_240
  | Nis_239
  | Nis_238
  | Nis_237
  | Nis_236
  | Nis_235
  | Nis_234
  | Nis_233
  | Nis_232
  | Nis_231
  | Nis_230
  | Nis_229
  | Nis_228
  | Nis_227
  | Nis_226
  | Nis_225
  | Nis_224
  | Nis_223
  | Nis_222
  | Nis_221
  | Nis_220
  | Nis_219
  | Nis_218
  | Nis_217
  | Nis_216
  | Nis_215
  | Nis_214
  | Nis_213
  | Nis_212
  | Nis_211
  | Nis_210
  | Nis_209
  | Nis_208
  | Nis_207
  | Nis_206
  | Nis_205
  | Nis_204
  | Nis_203
  | Nis_202
  | Nis_201
  | Nis_200
  | Nis_199
  | Nis_198
  | Nis_197
  | Nis_196
  | Nis_195
  | Nis_194
  | Nis_193
  | Nis_192
  | Nis_191
  | Nis_190
  | Nis_189
  | Nis_188
  | Nis_187
  | Nis_186
  | Nis_185
  | Nis_184
  | Nis_183
  | Nis_182
  | Nis_181
  | Nis_180
  | Nis_179
  | Nis_178
  | Nis_177
  | Nis_176
  | Nis_175
  | Nis_174
  | Nis_173
  | Nis_172
  | Nis_171
  | Nis_170
  | Nis_169
  | Nis_168
  | Nis_167
  | Nis_166
  | Nis_165
  | Nis_164
  | Nis_163
  | Nis_162
  | Nis_161
  | Nis_160
  | Nis_159
  | Nis_158
  | Nis_157
  | Nis_156
  | Nis_155
  | Nis_154
  | Nis_153
  | Nis_152
  | Nis_151
  | Nis_150
  | Nis_149
  | Nis_148
  | Nis_147
  | Nis_146
  | Nis_145
  | Nis_144
  | Nis_143
  | Nis_142
  | Nis_141
  | Nis_140
  | Nis_139
  | Nis_138
  | Nis_137
  | Nis_136
  | Nis_135
  | Nis_134
  | Nis_133
  | Nis_132
  | Nis_131
  | Nis_130
  | Nis_129
  | Nis_128
  | Nis_127
  | Nis_126
  | Nis_125
  | Nis_124
  | Nis_123
  | Nis_122
  | Nis_121
  | Nis_120
  | Nis_119
  | Nis_118
  | Nis_117
  | Nis_116
  | Nis_115
  | Nis_114
  | Nis_113
  | Nis_112
  | Nis_111
  | Nis_110
  | Nis_109
  | Nis_108
  | Nis_107
  | Nis_106
  | Nis_105
  | Nis_104
  | Nis_103
  | Nis_102
  | Nis_101
  | Nis_100
  | Nis_99
  | Nis_98
  | Nis_97
  | Nis_96
  | Nis_95
  | Nis_94
  | Nis_93
  | Nis_92
  | Nis_91
  | Nis_90
  | Nis_89
  | Nis_88
  | Nis_87
  | Nis_86
  | Nis_85
  | Nis_84
  | Nis_83
  | Nis_82
  | Nis_81
  | Nis_80
  | Nis_79
  | Nis_78
  | Nis_77
  | Nis_76
  | Nis_75
  | Nis_74
  | Nis_73
  | Nis_72
  | Nis_71
  | Nis_70
  | Nis_69
  | Nis_68
  | Nis_67
  | Nis_66
  | Nis_65
  | Nis_64
  | Nis_63
  | Nis_62
  | Nis_61
  | Nis_60
  | Nis_59
  | Nis_58
  | Nis_57
  | Nis_56
  | Nis_55
  | Nis_54
  | Nis_53
  | Nis_52
  | Nis_51
  | Nis_50
  | Nis_49
  | Nis_48
  | Nis_47
  | Nis_46
  | Nis_45
  | Nis_44
  | Nis_43
  | Nis_42
  | Nis_41
  | Nis_40
  | Nis_39
  | Nis_38
  | Nis_37
  | Nis_36
  | Nis_35
  | Nis_34
  | Nis_33
  | Nis_32
  | Nis_31
  | Nis_30
  | Nis_29
  | Nis_28
  | Nis_27
  | Nis_26
  | Nis_25
  | Nis_24
  | Nis_23
  | Nis_22
  | Nis_21
  | Nis_20
  | Nis_19
  | Nis_18
  | Nis_17
  | Nis_16
  | Nis_15
  | Nis_14
  | Nis_13
  | Nis_12
  | Nis_11
  | Nis_10
  | Nis_9
  | Nis_8
  | Nis_7
  | Nis_6
  | Nis_5
  | Nis_4
  | Nis_3
  | Nis_2
  | Nis_1
  
  val noninitstate'_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    noninitstate' -> 'a1
  
  val noninitstate'_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    noninitstate' -> 'a1
  
  type noninitstate = noninitstate'
  
  val noninitstateNum : noninitstate coq_Numbered
  
  val coq_NonInitStateAlph : noninitstate coq_Alphabet
  
  val last_symb_of_non_init_state : noninitstate -> Coq__1.symbol
  
  type state =
  | Init
  | Ninit of noninitstate
  
  val state_rect : 'a1 -> (noninitstate -> 'a1) -> state -> 'a1
  
  val state_rec : 'a1 -> (noninitstate -> 'a1) -> state -> 'a1
  
  val coq_StateAlph : state coq_Alphabet
  
  type action =
  | Shift_act of noninitstate
  | Reduce_act of Gram.production
  | Fail_act
  
  val action_rect :
    Gram.terminal -> (noninitstate -> __ -> 'a1) -> (Gram.production -> 'a1)
    -> 'a1 -> action -> 'a1
  
  val action_rec :
    Gram.terminal -> (noninitstate -> __ -> 'a1) -> (Gram.production -> 'a1)
    -> 'a1 -> action -> 'a1
  
  type default_action =
  | Default_reduce_act of Gram.production
  | Accept_act
  
  val default_action_rect :
    (Gram.production -> 'a1) -> 'a1 -> default_action -> 'a1
  
  val default_action_rec :
    (Gram.production -> 'a1) -> 'a1 -> default_action -> 'a1
  
  type pseudoprod = Gram.production option
  
  type item = { pseudoprod_item : pseudoprod; dot_pos_item : nat;
                lookaheads_item : Gram.terminal list }
  
  val item_rect :
    (pseudoprod -> nat -> Gram.terminal list -> 'a1) -> item -> 'a1
  
  val item_rec :
    (pseudoprod -> nat -> Gram.terminal list -> 'a1) -> item -> 'a1
  
  val pseudoprod_item : item -> pseudoprod
  
  val dot_pos_item : item -> nat
  
  val lookaheads_item : item -> Gram.terminal list
  
  val action_table : state -> (default_action, Coq__1.terminal -> action) sum
  
  val goto_table : state -> Coq__1.nonterminal -> noninitstate option
  
  val past_symb_of_non_init_state : noninitstate -> Coq__1.symbol list
  
  val past_state_of_non_init_state : noninitstate -> (state -> bool) list
  
  val items_of_state : state -> item list
 end

module Parser : 
 sig 
  module Inter : 
   sig 
    type 'a result =
    | Err
    | OK of 'a
    
    val result_rect : 'a2 -> ('a1 -> 'a2) -> 'a1 result -> 'a2
    
    val result_rec : 'a2 -> ('a1 -> 'a2) -> 'a1 result -> 'a2
    
    val bind : 'a1 result -> ('a1 -> 'a2 result) -> 'a2 result
    
    val bind2 : ('a1*'a2) result -> ('a1 -> 'a2 -> 'a3 result) -> 'a3 result
    
    val app_str : 'a1 list -> 'a1 coq_Stream -> 'a1 coq_Stream
    
    type stack =
    | Nil_stack
    | Cons_stack of Aut.noninitstate * Aut.Gram.symbol_semantic_type * stack
    
    val stack_rect :
      'a1 -> (Aut.noninitstate -> Aut.Gram.symbol_semantic_type -> stack ->
      'a1 -> 'a1) -> stack -> 'a1
    
    val stack_rec :
      'a1 -> (Aut.noninitstate -> Aut.Gram.symbol_semantic_type -> stack ->
      'a1 -> 'a1) -> stack -> 'a1
    
    val state_of_stack : stack -> Aut.state
    
    val pop :
      Aut.Gram.symbol list -> stack -> Aut.Gram.symbol list -> tuple ->
      (stack*tuple) result
    
    val reduce : stack -> Aut.Gram.production -> stack result
    
    type step_result =
    | Fail_sr
    | Accept_sr of Aut.Gram.symbol_semantic_type
       * Aut.GramDefs.token coq_Stream
    | Progress_sr of stack * Aut.GramDefs.token coq_Stream
    
    val step_result_rect :
      'a1 -> (Aut.Gram.symbol_semantic_type -> Aut.GramDefs.token coq_Stream
      -> 'a1) -> (stack -> Aut.GramDefs.token coq_Stream -> 'a1) ->
      step_result -> 'a1
    
    val step_result_rec :
      'a1 -> (Aut.Gram.symbol_semantic_type -> Aut.GramDefs.token coq_Stream
      -> 'a1) -> (stack -> Aut.GramDefs.token coq_Stream -> 'a1) ->
      step_result -> 'a1
    
    val step : stack -> Aut.GramDefs.token coq_Stream -> step_result result
    
    type parse_result =
    | Fail_pr
    | Timeout_pr
    | Parsed_pr of Aut.Gram.symbol_semantic_type
       * Aut.GramDefs.token coq_Stream
    
    val parse_result_rect :
      'a1 -> 'a1 -> (Aut.Gram.symbol_semantic_type -> Aut.GramDefs.token
      coq_Stream -> 'a1) -> parse_result -> 'a1
    
    val parse_result_rec :
      'a1 -> 'a1 -> (Aut.Gram.symbol_semantic_type -> Aut.GramDefs.token
      coq_Stream -> 'a1) -> parse_result -> 'a1
    
    val parse_fix :
      stack -> Aut.GramDefs.token coq_Stream -> nat -> parse_result result
    
    val parse : Aut.GramDefs.token coq_Stream -> nat -> parse_result result
   end
  
  module Safe : 
   sig 
    module Valid : 
     sig 
      val singleton_state_pred : Aut.state -> Aut.state -> bool
      
      val past_state_of_state : Aut.state -> (Aut.state -> bool) list
      
      val head_symbs_of_state : Aut.state -> Aut.Gram.symbol list
      
      val head_states_of_state : Aut.state -> (Aut.state -> bool) list
      
      val is_initial_no_accept : bool
      
      val is_accept_last_symb : bool
      
      val is_accept_initial : bool
      
      val is_prefix : Aut.Gram.symbol list -> Aut.Gram.symbol list -> bool
      
      val is_shift_head_symbs : bool
      
      val is_goto_head_symbs : bool
      
      val is_prefix_pred :
        (Aut.state -> bool) list -> (Aut.state -> bool) list -> bool
      
      val is_shift_past_state : bool
      
      val is_goto_past_state : bool
      
      val is_state_valid_after_pop :
        Aut.state -> Aut.Gram.symbol list -> (Aut.state -> bool) list -> bool
      
      val is_valid_for_reduce : Aut.state -> Aut.Gram.production -> bool
      
      val is_reduce_ok : bool
      
      val is_safe : bool
     end
    
    val symb_stack_of_stack : Inter.stack -> Aut.Gram.symbol list
    
    val state_stack_of_stack : Inter.stack -> (Aut.state -> bool) list
    
    val eq_rew_dep : 'a1 -> 'a2 -> 'a1 -> 'a2
    
    val parse_with_safe :
      Aut.GramDefs.token coq_Stream -> nat -> Inter.parse_result
   end
  
  module Correct : 
   sig 
    val eq_rew_r_dep : 'a1 -> 'a1 -> 'a2 -> 'a2
   end
  
  module Complete : 
   sig 
    module Valid : 
     sig 
      module TerminalComparableM : 
       sig 
        type t = Aut.Gram.terminal
        
        val tComparable : t coq_Comparable
       end
      
      module TerminalOrderedType : 
       sig 
        module Alt : 
         sig 
          type t = TerminalComparableM.t
          
          val compare : t -> t -> comparison
         end
        
        type t = Alt.t
        
        val compare : Alt.t -> Alt.t -> Alt.t OrderedType.coq_Compare
        
        val eq_dec : Alt.t -> Alt.t -> bool
       end
      
      module StatePseudoprodPosComparableM : 
       sig 
        type t = (Aut.state*Aut.pseudoprod)*nat
        
        val tComparable : t coq_Comparable
       end
      
      module StatePseudoprodPosOrderedType : 
       sig 
        module Alt : 
         sig 
          type t = StatePseudoprodPosComparableM.t
          
          val compare : t -> t -> comparison
         end
        
        type t = Alt.t
        
        val compare : Alt.t -> Alt.t -> Alt.t OrderedType.coq_Compare
        
        val eq_dec : Alt.t -> Alt.t -> bool
       end
      
      module TerminalSet : 
       sig 
        module X' : 
         sig 
          type t = TerminalOrderedType.Alt.t
          
          val eq_dec :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
          
          val compare :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
            comparison
         end
        
        module MSet : 
         sig 
          module Raw : 
           sig 
            type elt = TerminalOrderedType.Alt.t
            
            type tree =
            | Leaf
            | Node of tree * TerminalOrderedType.Alt.t * tree * Z_as_Int.int
            
            type t = tree
            
            val height : t -> Z_as_Int.int
            
            val cardinal : t -> nat
            
            val empty : tree
            
            val is_empty : tree -> bool
            
            val mem : TerminalOrderedType.Alt.t -> tree -> bool
            
            val singleton : TerminalOrderedType.Alt.t -> tree
            
            val create : tree -> TerminalOrderedType.Alt.t -> tree -> tree
            
            val assert_false :
              tree -> TerminalOrderedType.Alt.t -> tree -> tree
            
            val bal : t -> TerminalOrderedType.Alt.t -> t -> tree
            
            val add : TerminalOrderedType.Alt.t -> tree -> tree
            
            val join : tree -> elt -> t -> t
            
            val remove_min : tree -> elt -> t -> t*elt
            
            val merge : tree -> tree -> tree
            
            val remove : TerminalOrderedType.Alt.t -> tree -> tree
            
            val min_elt : tree -> TerminalOrderedType.Alt.t option
            
            val max_elt : tree -> TerminalOrderedType.Alt.t option
            
            val choose : tree -> TerminalOrderedType.Alt.t option
            
            val concat : tree -> tree -> tree
            
            type triple = { t_left : t; t_in : bool; t_right : t }
            
            val t_left : triple -> t
            
            val t_in : triple -> bool
            
            val t_right : triple -> t
            
            val split : TerminalOrderedType.Alt.t -> tree -> triple
            
            val inter : tree -> tree -> tree
            
            val diff : tree -> tree -> tree
            
            val union : tree -> tree -> tree
            
            val elements_aux :
              TerminalOrderedType.Alt.t list -> t ->
              TerminalOrderedType.Alt.t list
            
            val elements : t -> TerminalOrderedType.Alt.t list
            
            val filter_acc : (elt -> bool) -> tree -> tree -> tree
            
            val filter : (elt -> bool) -> tree -> tree
            
            val partition_acc : (elt -> bool) -> (t*t) -> t -> t*t
            
            val partition : (elt -> bool) -> t -> t*t
            
            val for_all : (elt -> bool) -> tree -> bool
            
            val exists_ : (elt -> bool) -> tree -> bool
            
            val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
            
            val subsetl :
              (t -> bool) -> TerminalOrderedType.Alt.t -> tree -> bool
            
            val subsetr :
              (t -> bool) -> TerminalOrderedType.Alt.t -> tree -> bool
            
            val subset : tree -> tree -> bool
            
            type enumeration =
            | End
            | More of elt * t * enumeration
            
            val cons : tree -> enumeration -> enumeration
            
            val compare_more :
              TerminalOrderedType.Alt.t -> (enumeration -> comparison) ->
              enumeration -> comparison
            
            val compare_cont :
              tree -> (enumeration -> comparison) -> enumeration ->
              comparison
            
            val compare_end : enumeration -> comparison
            
            val compare : tree -> tree -> comparison
            
            val equal : tree -> tree -> bool
            
            val ltb_tree : TerminalOrderedType.Alt.t -> tree -> bool
            
            val gtb_tree : TerminalOrderedType.Alt.t -> tree -> bool
            
            val isok : tree -> bool
            
            module MX : 
             sig 
              module OrderTac : 
               sig 
                module OTF : 
                 sig 
                  type t = TerminalOrderedType.Alt.t
                  
                  val compare :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    comparison
                  
                  val eq_dec :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    bool
                 end
                
                module TO : 
                 sig 
                  type t = TerminalOrderedType.Alt.t
                  
                  val compare :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    comparison
                  
                  val eq_dec :
                    TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                    bool
                 end
               end
              
              val eq_dec :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                bool
              
              val lt_dec :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                bool
              
              val eqb :
                TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                bool
             end
            
            type coq_R_bal =
            | R_bal_0 of t * TerminalOrderedType.Alt.t * t
            | R_bal_1 of t * TerminalOrderedType.Alt.t * t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.int
            | R_bal_2 of t * TerminalOrderedType.Alt.t * t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.int
            | R_bal_3 of t * TerminalOrderedType.Alt.t * t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.int * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.int
            | R_bal_4 of t * TerminalOrderedType.Alt.t * t
            | R_bal_5 of t * TerminalOrderedType.Alt.t * t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.int
            | R_bal_6 of t * TerminalOrderedType.Alt.t * t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.int
            | R_bal_7 of t * TerminalOrderedType.Alt.t * t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.int * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.int
            | R_bal_8 of t * TerminalOrderedType.Alt.t * t
            
            type coq_R_remove_min =
            | R_remove_min_0 of tree * elt * t
            | R_remove_min_1 of tree * elt * t * tree
               * TerminalOrderedType.Alt.t * tree * Z_as_Int.int * (t*elt)
               * coq_R_remove_min * t * elt
            
            type coq_R_merge =
            | R_merge_0 of tree * tree
            | R_merge_1 of tree * tree * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int
            | R_merge_2 of tree * tree * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * t * elt
            
            type coq_R_min_elt =
            | R_min_elt_0 of tree
            | R_min_elt_1 of tree * tree * TerminalOrderedType.Alt.t * 
               tree * Z_as_Int.int
            | R_min_elt_2 of tree * tree * TerminalOrderedType.Alt.t * 
               tree * Z_as_Int.int * tree * TerminalOrderedType.Alt.t * 
               tree * Z_as_Int.int * TerminalOrderedType.Alt.t option
               * coq_R_min_elt
            
            type coq_R_max_elt =
            | R_max_elt_0 of tree
            | R_max_elt_1 of tree * tree * TerminalOrderedType.Alt.t * 
               tree * Z_as_Int.int
            | R_max_elt_2 of tree * tree * TerminalOrderedType.Alt.t * 
               tree * Z_as_Int.int * tree * TerminalOrderedType.Alt.t * 
               tree * Z_as_Int.int * TerminalOrderedType.Alt.t option
               * coq_R_max_elt
            
            type coq_R_concat =
            | R_concat_0 of tree * tree
            | R_concat_1 of tree * tree * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int
            | R_concat_2 of tree * tree * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * t * elt
            
            type coq_R_inter =
            | R_inter_0 of tree * tree
            | R_inter_1 of tree * tree * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int
            | R_inter_2 of tree * tree * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * t * bool * t * tree * coq_R_inter
               * tree * coq_R_inter
            | R_inter_3 of tree * tree * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * t * bool * t * tree * coq_R_inter
               * tree * coq_R_inter
            
            type coq_R_diff =
            | R_diff_0 of tree * tree
            | R_diff_1 of tree * tree * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int
            | R_diff_2 of tree * tree * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * t * bool * t * tree * coq_R_diff
               * tree * coq_R_diff
            | R_diff_3 of tree * tree * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * t * bool * t * tree * coq_R_diff
               * tree * coq_R_diff
            
            type coq_R_union =
            | R_union_0 of tree * tree
            | R_union_1 of tree * tree * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int
            | R_union_2 of tree * tree * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * tree * TerminalOrderedType.Alt.t
               * tree * Z_as_Int.int * t * bool * t * tree * coq_R_union
               * tree * coq_R_union
            
            module L : 
             sig 
              module MO : 
               sig 
                module OrderTac : 
                 sig 
                  module OTF : 
                   sig 
                    type t = TerminalOrderedType.Alt.t
                    
                    val compare :
                      TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t
                      -> comparison
                    
                    val eq_dec :
                      TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t
                      -> bool
                   end
                  
                  module TO : 
                   sig 
                    type t = TerminalOrderedType.Alt.t
                    
                    val compare :
                      TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t
                      -> comparison
                    
                    val eq_dec :
                      TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t
                      -> bool
                   end
                 end
                
                val eq_dec :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  bool
                
                val lt_dec :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  bool
                
                val eqb :
                  TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
                  bool
               end
             end
            
            val flatten_e : enumeration -> elt list
           end
          
          module E : 
           sig 
            type t = TerminalOrderedType.Alt.t
            
            val compare :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
              comparison
            
            val eq_dec :
              TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
           end
          
          type elt = TerminalOrderedType.Alt.t
          
          type t_ =
            Raw.t
            (* singleton inductive, whose constructor was Mkt *)
          
          val this : t_ -> Raw.t
          
          type t = t_
          
          val mem : elt -> t -> bool
          
          val add : elt -> t -> t
          
          val remove : elt -> t -> t
          
          val singleton : elt -> t
          
          val union : t -> t -> t
          
          val inter : t -> t -> t
          
          val diff : t -> t -> t
          
          val equal : t -> t -> bool
          
          val subset : t -> t -> bool
          
          val empty : t
          
          val is_empty : t -> bool
          
          val elements : t -> elt list
          
          val choose : t -> elt option
          
          val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
          
          val cardinal : t -> nat
          
          val filter : (elt -> bool) -> t -> t
          
          val for_all : (elt -> bool) -> t -> bool
          
          val exists_ : (elt -> bool) -> t -> bool
          
          val partition : (elt -> bool) -> t -> t*t
          
          val eq_dec : t -> t -> bool
          
          val compare : t -> t -> comparison
          
          val min_elt : t -> elt option
          
          val max_elt : t -> elt option
         end
        
        type elt = TerminalOrderedType.Alt.t
        
        type t = MSet.t
        
        val empty : t
        
        val is_empty : t -> bool
        
        val mem : elt -> t -> bool
        
        val add : elt -> t -> t
        
        val singleton : elt -> t
        
        val remove : elt -> t -> t
        
        val union : t -> t -> t
        
        val inter : t -> t -> t
        
        val diff : t -> t -> t
        
        val eq_dec : t -> t -> bool
        
        val equal : t -> t -> bool
        
        val subset : t -> t -> bool
        
        val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1
        
        val for_all : (elt -> bool) -> t -> bool
        
        val exists_ : (elt -> bool) -> t -> bool
        
        val filter : (elt -> bool) -> t -> t
        
        val partition : (elt -> bool) -> t -> t*t
        
        val cardinal : t -> nat
        
        val elements : t -> elt list
        
        val choose : t -> elt option
        
        module MF : 
         sig 
          val eqb :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
         end
        
        val min_elt : t -> elt option
        
        val max_elt : t -> elt option
        
        val compare : t -> t -> t OrderedType.coq_Compare
        
        module E : 
         sig 
          type t = TerminalOrderedType.Alt.t
          
          val compare :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t ->
            TerminalOrderedType.Alt.t OrderedType.coq_Compare
          
          val eq_dec :
            TerminalOrderedType.Alt.t -> TerminalOrderedType.Alt.t -> bool
         end
       end
      
      module StatePseudoprodPosMap : 
       sig 
        module E : 
         sig 
          type t = StatePseudoprodPosOrderedType.Alt.t
          
          val compare :
            StatePseudoprodPosOrderedType.Alt.t ->
            StatePseudoprodPosOrderedType.Alt.t ->
            StatePseudoprodPosOrderedType.Alt.t OrderedType.coq_Compare
          
          val eq_dec :
            StatePseudoprodPosOrderedType.Alt.t ->
            StatePseudoprodPosOrderedType.Alt.t -> bool
         end
        
        module Raw : 
         sig 
          type key = StatePseudoprodPosOrderedType.Alt.t
          
          type 'elt tree =
          | Leaf
          | Node of 'elt tree * key * 'elt * 'elt tree * Z_as_Int.int
          
          val tree_rect :
            'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
            Z_as_Int.int -> 'a2) -> 'a1 tree -> 'a2
          
          val tree_rec :
            'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 ->
            Z_as_Int.int -> 'a2) -> 'a1 tree -> 'a2
          
          val height : 'a1 tree -> Z_as_Int.int
          
          val cardinal : 'a1 tree -> nat
          
          val empty : 'a1 tree
          
          val is_empty : 'a1 tree -> bool
          
          val mem : StatePseudoprodPosOrderedType.Alt.t -> 'a1 tree -> bool
          
          val find :
            StatePseudoprodPosOrderedType.Alt.t -> 'a1 tree -> 'a1 option
          
          val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
          
          val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
          
          val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
          
          val add : key -> 'a1 -> 'a1 tree -> 'a1 tree
          
          val remove_min :
            'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree*(key*'a1)
          
          val merge : 'a1 tree -> 'a1 tree -> 'a1 tree
          
          val remove :
            StatePseudoprodPosOrderedType.Alt.t -> 'a1 tree -> 'a1 tree
          
          val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree
          
          type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                               t_right : 'elt tree }
          
          val triple_rect :
            ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
          
          val triple_rec :
            ('a1 tree -> 'a1 option -> 'a1 tree -> 'a2) -> 'a1 triple -> 'a2
          
          val t_left : 'a1 triple -> 'a1 tree
          
          val t_opt : 'a1 triple -> 'a1 option
          
          val t_right : 'a1 triple -> 'a1 tree
          
          val split :
            StatePseudoprodPosOrderedType.Alt.t -> 'a1 tree -> 'a1 triple
          
          val concat : 'a1 tree -> 'a1 tree -> 'a1 tree
          
          val elements_aux : (key*'a1) list -> 'a1 tree -> (key*'a1) list
          
          val elements : 'a1 tree -> (key*'a1) list
          
          val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
          
          type 'elt enumeration =
          | End
          | More of key * 'elt * 'elt tree * 'elt enumeration
          
          val enumeration_rect :
            'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2)
            -> 'a1 enumeration -> 'a2
          
          val enumeration_rec :
            'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2)
            -> 'a1 enumeration -> 'a2
          
          val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration
          
          val equal_more :
            ('a1 -> 'a1 -> bool) -> StatePseudoprodPosOrderedType.Alt.t ->
            'a1 -> ('a1 enumeration -> bool) -> 'a1 enumeration -> bool
          
          val equal_cont :
            ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) ->
            'a1 enumeration -> bool
          
          val equal_end : 'a1 enumeration -> bool
          
          val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool
          
          val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree
          
          val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree
          
          val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree
          
          val map2_opt :
            (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
            tree) -> ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3
            tree
          
          val map2 :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree
            -> 'a3 tree
          
          module Proofs : 
           sig 
            module MX : 
             sig 
              module OrderElts : 
               sig 
                type t = StatePseudoprodPosOrderedType.Alt.t
               end
              
              module OrderTac : 
               sig 
                
               end
              
              val eq_dec :
                StatePseudoprodPosOrderedType.Alt.t ->
                StatePseudoprodPosOrderedType.Alt.t -> bool
              
              val lt_dec :
                StatePseudoprodPosOrderedType.Alt.t ->
                StatePseudoprodPosOrderedType.Alt.t -> bool
              
              val eqb :
                StatePseudoprodPosOrderedType.Alt.t ->
                StatePseudoprodPosOrderedType.Alt.t -> bool
             end
            
            module PX : 
             sig 
              module MO : 
               sig 
                module OrderElts : 
                 sig 
                  type t = StatePseudoprodPosOrderedType.Alt.t
                 end
                
                module OrderTac : 
                 sig 
                  
                 end
                
                val eq_dec :
                  StatePseudoprodPosOrderedType.Alt.t ->
                  StatePseudoprodPosOrderedType.Alt.t -> bool
                
                val lt_dec :
                  StatePseudoprodPosOrderedType.Alt.t ->
                  StatePseudoprodPosOrderedType.Alt.t -> bool
                
                val eqb :
                  StatePseudoprodPosOrderedType.Alt.t ->
                  StatePseudoprodPosOrderedType.Alt.t -> bool
               end
             end
            
            module L : 
             sig 
              module MX : 
               sig 
                module OrderElts : 
                 sig 
                  type t = StatePseudoprodPosOrderedType.Alt.t
                 end
                
                module OrderTac : 
                 sig 
                  
                 end
                
                val eq_dec :
                  StatePseudoprodPosOrderedType.Alt.t ->
                  StatePseudoprodPosOrderedType.Alt.t -> bool
                
                val lt_dec :
                  StatePseudoprodPosOrderedType.Alt.t ->
                  StatePseudoprodPosOrderedType.Alt.t -> bool
                
                val eqb :
                  StatePseudoprodPosOrderedType.Alt.t ->
                  StatePseudoprodPosOrderedType.Alt.t -> bool
               end
              
              module PX : 
               sig 
                module MO : 
                 sig 
                  module OrderElts : 
                   sig 
                    type t = StatePseudoprodPosOrderedType.Alt.t
                   end
                  
                  module OrderTac : 
                   sig 
                    
                   end
                  
                  val eq_dec :
                    StatePseudoprodPosOrderedType.Alt.t ->
                    StatePseudoprodPosOrderedType.Alt.t -> bool
                  
                  val lt_dec :
                    StatePseudoprodPosOrderedType.Alt.t ->
                    StatePseudoprodPosOrderedType.Alt.t -> bool
                  
                  val eqb :
                    StatePseudoprodPosOrderedType.Alt.t ->
                    StatePseudoprodPosOrderedType.Alt.t -> bool
                 end
               end
              
              type key = StatePseudoprodPosOrderedType.Alt.t
              
              type 'elt t = (StatePseudoprodPosOrderedType.Alt.t*'elt) list
              
              val empty : 'a1 t
              
              val is_empty : 'a1 t -> bool
              
              val mem : key -> 'a1 t -> bool
              
              type 'elt coq_R_mem =
              | R_mem_0 of 'elt t
              | R_mem_1 of 'elt t * StatePseudoprodPosOrderedType.Alt.t
                 * 'elt * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
              | R_mem_2 of 'elt t * StatePseudoprodPosOrderedType.Alt.t
                 * 'elt * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
              | R_mem_3 of 'elt t * StatePseudoprodPosOrderedType.Alt.t
                 * 'elt * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
                 * bool * 'elt coq_R_mem
              
              val coq_R_mem_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool
                -> 'a1 coq_R_mem -> 'a2
              
              val coq_R_mem_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool
                -> 'a1 coq_R_mem -> 'a2
              
              val mem_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
              
              val mem_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
              
              val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem
              
              val find : key -> 'a1 t -> 'a1 option
              
              type 'elt coq_R_find =
              | R_find_0 of 'elt t
              | R_find_1 of 'elt t * StatePseudoprodPosOrderedType.Alt.t
                 * 'elt * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
              | R_find_2 of 'elt t * StatePseudoprodPosOrderedType.Alt.t
                 * 'elt * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
              | R_find_3 of 'elt t * StatePseudoprodPosOrderedType.Alt.t
                 * 'elt * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
                 * 'elt option * 'elt coq_R_find
              
              val coq_R_find_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t ->
                'a1 option -> 'a1 coq_R_find -> 'a2
              
              val coq_R_find_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t ->
                'a1 option -> 'a1 coq_R_find -> 'a2
              
              val find_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
              
              val find_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
              
              val coq_R_find_correct :
                key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find
              
              val add : key -> 'a1 -> 'a1 t -> 'a1 t
              
              type 'elt coq_R_add =
              | R_add_0 of 'elt t
              | R_add_1 of 'elt t * StatePseudoprodPosOrderedType.Alt.t
                 * 'elt * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
              | R_add_2 of 'elt t * StatePseudoprodPosOrderedType.Alt.t
                 * 'elt * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
              | R_add_3 of 'elt t * StatePseudoprodPosOrderedType.Alt.t
                 * 'elt * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
                 * 'elt t * 'elt coq_R_add
              
              val coq_R_add_rect :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
                -> 'a1 coq_R_add -> 'a2
              
              val coq_R_add_rec :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
                -> 'a1 coq_R_add -> 'a2
              
              val add_rect :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
              
              val add_rec :
                key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
              
              val coq_R_add_correct :
                key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
              
              val remove : key -> 'a1 t -> 'a1 t
              
              type 'elt coq_R_remove =
              | R_remove_0 of 'elt t
              | R_remove_1 of 'elt t * StatePseudoprodPosOrderedType.Alt.t
                 * 'elt * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
              | R_remove_2 of 'elt t * StatePseudoprodPosOrderedType.Alt.t
                 * 'elt * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
              | R_remove_3 of 'elt t * StatePseudoprodPosOrderedType.Alt.t
                 * 'elt * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
                 * 'elt t * 'elt coq_R_remove
              
              val coq_R_remove_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t ->
                'a1 t -> 'a1 coq_R_remove -> 'a2
              
              val coq_R_remove_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t ->
                'a1 t -> 'a1 coq_R_remove -> 'a2
              
              val remove_rect :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
              
              val remove_rec :
                key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2) -> ('a1 t -> StatePseudoprodPosOrderedType.Alt.t
                -> 'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list ->
                __ -> __ -> __ -> 'a2) -> ('a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2
              
              val coq_R_remove_correct :
                key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
              
              val elements : 'a1 t -> 'a1 t
              
              val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
              
              type ('elt, 'a) coq_R_fold =
              | R_fold_0 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
              | R_fold_1 of (key -> 'elt -> 'a -> 'a) * 'elt t * 'a
                 * StatePseudoprodPosOrderedType.Alt.t * 'elt
                 * (StatePseudoprodPosOrderedType.Alt.t*'elt) list * 
                 'a * ('elt, 'a) coq_R_fold
              
              val coq_R_fold_rect :
                (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2)
                -> (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                ('a1, __) coq_R_fold -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 ->
                'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold -> 'a2
              
              val coq_R_fold_rec :
                (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2)
                -> (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                ('a1, __) coq_R_fold -> 'a2 -> 'a2) -> (key -> 'a1 -> 'a3 ->
                'a3) -> 'a1 t -> 'a3 -> 'a3 -> ('a1, 'a3) coq_R_fold -> 'a2
              
              val fold_rect :
                (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2)
                -> (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> 'a2
                -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a2
              
              val fold_rec :
                (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ -> __ -> 'a2)
                -> (__ -> (key -> 'a1 -> __ -> __) -> 'a1 t -> __ ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> 'a2
                -> 'a2) -> (key -> 'a1 -> 'a3 -> 'a3) -> 'a1 t -> 'a3 -> 'a2
              
              val coq_R_fold_correct :
                (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1,
                'a2) coq_R_fold
              
              val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
              
              type 'elt coq_R_equal =
              | R_equal_0 of 'elt t * 'elt t
              | R_equal_1 of 'elt t * 'elt t
                 * StatePseudoprodPosOrderedType.Alt.t * 'elt
                 * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
                 * StatePseudoprodPosOrderedType.Alt.t * 'elt
                 * (StatePseudoprodPosOrderedType.Alt.t*'elt) list * 
                 bool * 'elt coq_R_equal
              | R_equal_2 of 'elt t * 'elt t
                 * StatePseudoprodPosOrderedType.Alt.t * 'elt
                 * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
                 * StatePseudoprodPosOrderedType.Alt.t * 'elt
                 * (StatePseudoprodPosOrderedType.Alt.t*'elt) list
                 * StatePseudoprodPosOrderedType.Alt.t
                   OrderedType.coq_Compare
              | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t
              
              val coq_R_equal_rect :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> StatePseudoprodPosOrderedType.Alt.t ->
                'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __
                -> StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1
                t -> StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ ->
                StatePseudoprodPosOrderedType.Alt.t OrderedType.coq_Compare
                -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1
                t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1
                coq_R_equal -> 'a2
              
              val coq_R_equal_rec :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> StatePseudoprodPosOrderedType.Alt.t ->
                'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __
                -> StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> bool -> 'a1 coq_R_equal -> 'a2 -> 'a2) -> ('a1 t -> 'a1
                t -> StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ ->
                StatePseudoprodPosOrderedType.Alt.t OrderedType.coq_Compare
                -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1
                t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> bool -> 'a1
                coq_R_equal -> 'a2
              
              val equal_rect :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> StatePseudoprodPosOrderedType.Alt.t ->
                'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __
                -> StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ ->
                StatePseudoprodPosOrderedType.Alt.t OrderedType.coq_Compare
                -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1
                t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2
              
              val equal_rec :
                ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2)
                -> ('a1 t -> 'a1 t -> StatePseudoprodPosOrderedType.Alt.t ->
                'a1 -> (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __
                -> StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ -> __ ->
                __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ ->
                StatePseudoprodPosOrderedType.Alt.t -> 'a1 ->
                (StatePseudoprodPosOrderedType.Alt.t*'a1) list -> __ ->
                StatePseudoprodPosOrderedType.Alt.t OrderedType.coq_Compare
                -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1
                t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2
              
              val coq_R_equal_correct :
                ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1
                coq_R_equal
              
              val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
              
              val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
              
              val option_cons :
                key -> 'a1 option -> (key*'a1) list -> (key*'a1) list
              
              val map2_l :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t
              
              val map2_r :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t
              
              val map2 :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
                'a3 t
              
              val combine : 'a1 t -> 'a2 t -> ('a1 option*'a2 option) t
              
              val fold_right_pair :
                ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1*'a2) list -> 'a3 -> 'a3
              
              val map2_alt :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
                (key*'a3) list
              
              val at_least_one :
                'a1 option -> 'a2 option -> ('a1 option*'a2 option) option
              
              val at_least_one_then_f :
                ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2
                option -> 'a3 option
             end
            
            type 'elt coq_R_mem =
            | R_mem_0 of 'elt tree
            | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.int * bool * 'elt coq_R_mem
            | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.int
            | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.int * bool * 'elt coq_R_mem
            
            val coq_R_mem_rect :
              StatePseudoprodPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2)
              -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
              -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ ->
              bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1
              coq_R_mem -> 'a2
            
            val coq_R_mem_rec :
              StatePseudoprodPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2)
              -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
              -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ ->
              bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 tree -> bool -> 'a1
              coq_R_mem -> 'a2
            
            type 'elt coq_R_find =
            | R_find_0 of 'elt tree
            | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.int * 'elt option * 'elt coq_R_find
            | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.int
            | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.int * 'elt option * 'elt coq_R_find
            
            val coq_R_find_rect :
              StatePseudoprodPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2)
              -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
              -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __
              -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
              tree -> 'a1 option -> 'a1 coq_R_find -> 'a2
            
            val coq_R_find_rec :
              StatePseudoprodPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2)
              -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
              -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __
              -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1
              tree -> 'a1 option -> 'a1 coq_R_find -> 'a2
            
            type 'elt coq_R_bal =
            | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
            | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Z_as_Int.int
            | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Z_as_Int.int
            | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Z_as_Int.int * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.int
            | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
            | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Z_as_Int.int
            | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Z_as_Int.int
            | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
               key * 'elt * 'elt tree * Z_as_Int.int * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.int
            | R_bal_8 of 'elt tree * key * 'elt * 'elt tree
            
            val coq_R_bal_rect :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2)
              -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ ->
              __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
              -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int ->
              __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
              tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key
              -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key
              -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) ->
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __
              -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree ->
              __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.int -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
              -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key
              -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2
            
            val coq_R_bal_rec :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2)
              -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ ->
              'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ ->
              __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __
              -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int ->
              __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
              tree -> __ -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key
              -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1 tree -> key
              -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) ->
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __
              -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree ->
              __ -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.int -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
              -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key
              -> 'a1 -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2
            
            type 'elt coq_R_add =
            | R_add_0 of 'elt tree
            | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.int * 'elt tree * 'elt coq_R_add
            | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.int
            | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.int * 'elt tree * 'elt coq_R_add
            
            val coq_R_add_rect :
              key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ ->
              'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ ->
              __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add
              -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2
            
            val coq_R_add_rec :
              key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree
              -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ ->
              'a1 tree -> 'a1 coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1
              tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ ->
              __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_add
              -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add -> 'a2
            
            type 'elt coq_R_remove_min =
            | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
            | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree
               * 'elt tree * key * 'elt * 'elt tree * Z_as_Int.int
               * ('elt tree*(key*'elt)) * 'elt coq_R_remove_min * 'elt tree
               * (key*'elt)
            
            val coq_R_remove_min_rect :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
              -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.int -> __ -> ('a1 tree*(key*'a1)) -> 'a1
              coq_R_remove_min -> 'a2 -> 'a1 tree -> (key*'a1) -> __ -> 'a2)
              -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree*(key*'a1))
              -> 'a1 coq_R_remove_min -> 'a2
            
            val coq_R_remove_min_rec :
              ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree
              -> key -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree
              -> Z_as_Int.int -> __ -> ('a1 tree*(key*'a1)) -> 'a1
              coq_R_remove_min -> 'a2 -> 'a1 tree -> (key*'a1) -> __ -> 'a2)
              -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree*(key*'a1))
              -> 'a1 coq_R_remove_min -> 'a2
            
            type 'elt coq_R_merge =
            | R_merge_0 of 'elt tree * 'elt tree
            | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.int
            | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.int * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.int * 'elt tree * (key*'elt) * 
               key * 'elt
            
            val coq_R_merge_rect :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Z_as_Int.int -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.int -> __ -> 'a1 tree -> (key*'a1) -> __ ->
              key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
              'a1 coq_R_merge -> 'a2
            
            val coq_R_merge_rec :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Z_as_Int.int -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.int -> __ -> 'a1 tree -> (key*'a1) -> __ ->
              key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree ->
              'a1 coq_R_merge -> 'a2
            
            type 'elt coq_R_remove =
            | R_remove_0 of 'elt tree
            | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.int * 'elt tree * 'elt coq_R_remove
            | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.int
            | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.int * 'elt tree * 'elt coq_R_remove
            
            val coq_R_remove_rect :
              StatePseudoprodPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2)
              -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
              -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __
              -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1
              tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2
            
            val coq_R_remove_rec :
              StatePseudoprodPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2)
              -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
              -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a2) -> ('a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __
              -> __ -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1
              tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2
            
            type 'elt coq_R_concat =
            | R_concat_0 of 'elt tree * 'elt tree
            | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.int
            | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.int * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.int * 'elt tree * (key*'elt)
            
            val coq_R_concat_rect :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Z_as_Int.int -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.int -> __ -> 'a1 tree -> (key*'a1) -> __ ->
              'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat ->
              'a2
            
            val coq_R_concat_rec :
              ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree ->
              'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __
              -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Z_as_Int.int -> __ -> 'a1 tree -> key -> 'a1 -> 'a1
              tree -> Z_as_Int.int -> __ -> 'a1 tree -> (key*'a1) -> __ ->
              'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_concat ->
              'a2
            
            type 'elt coq_R_split =
            | R_split_0 of 'elt tree
            | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.int * 'elt triple * 'elt coq_R_split * 'elt tree
               * 'elt option * 'elt tree
            | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.int
            | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree
               * Z_as_Int.int * 'elt triple * 'elt coq_R_split * 'elt tree
               * 'elt option * 'elt tree
            
            val coq_R_split_rect :
              StatePseudoprodPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2)
              -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
              -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int
              -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
              'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 triple
              -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree
              -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split ->
              'a2
            
            val coq_R_split_rec :
              StatePseudoprodPosOrderedType.Alt.t -> ('a1 tree -> __ -> 'a2)
              -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
              -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) ->
              ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int
              -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key ->
              'a1 -> 'a1 tree -> Z_as_Int.int -> __ -> __ -> __ -> 'a1 triple
              -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree
              -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1 coq_R_split ->
              'a2
            
            type ('elt, 'elt') coq_R_map_option =
            | R_map_option_0 of 'elt tree
            | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.int * 'elt' * 'elt' tree
               * ('elt, 'elt') coq_R_map_option * 'elt' tree
               * ('elt, 'elt') coq_R_map_option
            | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt
               * 'elt tree * Z_as_Int.int * 'elt' tree
               * ('elt, 'elt') coq_R_map_option * 'elt' tree
               * ('elt, 'elt') coq_R_map_option
            
            val coq_R_map_option_rect :
              (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int ->
              __ -> 'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
              'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3)
              -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
              coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
              coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree ->
              ('a1, 'a2) coq_R_map_option -> 'a3
            
            val coq_R_map_option_rec :
              (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1
              tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int ->
              __ -> 'a2 -> __ -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
              'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a3)
              -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
              coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
              coq_R_map_option -> 'a3 -> 'a3) -> 'a1 tree -> 'a2 tree ->
              ('a1, 'a2) coq_R_map_option -> 'a3
            
            type ('elt, 'elt', 'elt'') coq_R_map2_opt =
            | R_map2_opt_0 of 'elt tree * 'elt' tree
            | R_map2_opt_1 of 'elt tree * 'elt' tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.int
            | R_map2_opt_2 of 'elt tree * 'elt' tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.int * 'elt' tree * key * 'elt'
               * 'elt' tree * Z_as_Int.int * 'elt' tree * 'elt' option
               * 'elt' tree * 'elt'' * 'elt'' tree
               * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
               * ('elt, 'elt', 'elt'') coq_R_map2_opt
            | R_map2_opt_3 of 'elt tree * 'elt' tree * 'elt tree * key * 
               'elt * 'elt tree * Z_as_Int.int * 'elt' tree * key * 'elt'
               * 'elt' tree * Z_as_Int.int * 'elt' tree * 'elt' option
               * 'elt' tree * 'elt'' tree
               * ('elt, 'elt', 'elt'') coq_R_map2_opt * 'elt'' tree
               * ('elt, 'elt', 'elt'') coq_R_map2_opt
            
            val coq_R_map2_opt_rect :
              (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
              tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __
              -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Z_as_Int.int -> __ -> __ -> 'a4) -> ('a1 tree ->
              'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int
              -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.int ->
              __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ ->
              'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree
              -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree
              -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree ->
              Z_as_Int.int -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __
              -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
              'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) ->
              'a1 tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3)
              coq_R_map2_opt -> 'a4
            
            val coq_R_map2_opt_rec :
              (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3
              tree) -> ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __
              -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 ->
              'a1 tree -> Z_as_Int.int -> __ -> __ -> 'a4) -> ('a1 tree ->
              'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> Z_as_Int.int
              -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> Z_as_Int.int ->
              __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ ->
              'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree
              -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree
              -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
              Z_as_Int.int -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree ->
              Z_as_Int.int -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __
              -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 ->
              'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) ->
              'a1 tree -> 'a2 tree -> 'a3 tree -> ('a1, 'a2, 'a3)
              coq_R_map2_opt -> 'a4
            
            val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2
            
            val flatten_e : 'a1 enumeration -> (key*'a1) list
           end
         end
        
        type 'elt bst =
          'elt Raw.tree
          (* singleton inductive, whose constructor was Bst *)
        
        val bst_rect : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2
        
        val bst_rec : ('a1 Raw.tree -> __ -> 'a2) -> 'a1 bst -> 'a2
        
        val this : 'a1 bst -> 'a1 Raw.tree
        
        type 'elt t = 'elt bst
        
        type key = StatePseudoprodPosOrderedType.Alt.t
        
        val empty : 'a1 t
        
        val is_empty : 'a1 t -> bool
        
        val add : key -> 'a1 -> 'a1 t -> 'a1 t
        
        val remove : key -> 'a1 t -> 'a1 t
        
        val mem : key -> 'a1 t -> bool
        
        val find : key -> 'a1 t -> 'a1 option
        
        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
        
        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
        
        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t
        
        val elements : 'a1 t -> (key*'a1) list
        
        val cardinal : 'a1 t -> nat
        
        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
        
        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
       end
      
      val pseudoprod_rhs : Aut.Gram.production option -> Aut.Gram.symbol list
      
      val nullable_symb : Aut.Gram.symbol -> bool
      
      val nullable_word : Aut.Gram.symbol list -> bool
      
      val first_nterm_set : Aut.Gram.nonterminal -> TerminalSet.t
      
      val first_symb_set : Aut.Gram.symbol -> TerminalSet.t
      
      val first_word_set : Aut.Gram.symbol list -> TerminalSet.t
      
      val future_of_pseudoprod :
        Aut.Gram.production option -> nat -> Aut.Gram.symbol list
      
      val items_map : TerminalSet.t StatePseudoprodPosMap.t
      
      val find_items_map :
        Aut.state -> Aut.pseudoprod -> nat -> TerminalSet.t
      
      val forallb_items :
        (Aut.state -> Aut.pseudoprod -> nat -> TerminalSet.t -> bool) -> bool
      
      val is_nullable_stable : bool
      
      val is_first_stable : bool
      
      val is_end_accept : bool
      
      val is_start_future : bool
      
      val is_terminal_shift : bool
      
      val is_end_reduce : bool
      
      val is_non_terminal_goto : bool
      
      val is_non_terminal_closed : bool
      
      val is_complete : bool
     end
    
    val first_term_word :
      Aut.GramDefs.token list -> Aut.Gram.terminal -> Aut.Gram.terminal
    
    val extend_stack :
      Inter.stack -> Aut.noninitstate list -> __ -> Inter.stack
    
    type past_invariant = { states_pi : Aut.noninitstate list; sem_pi : tuple }
    
    val past_invariant_rect :
      (Aut.noninitstate list -> tuple -> 'a1) -> past_invariant -> 'a1
    
    val past_invariant_rec :
      (Aut.noninitstate list -> tuple -> 'a1) -> past_invariant -> 'a1
    
    val states_pi : past_invariant -> Aut.noninitstate list
    
    val symbl_pi : past_invariant -> Aut.Gram.symbol list
    
    val sem_pi : past_invariant -> tuple
    
    val stack_pi : past_invariant -> Inter.stack -> Inter.stack
    
    type hole_future_invariant = { future_hfi : (Aut.Gram.symbol list, tuple)
                                                sigT;
                                   word_future_hfi : Aut.GramDefs.token list;
                                   future_sem_proof_hfi : Aut.GramDefs.parse_tree_list;
                                   hole_hfi : (Aut.Gram.production, tuple)
                                              sigT option }
    
    val hole_future_invariant_rect :
      bool -> ((Aut.Gram.symbol list, tuple) sigT -> __ -> Aut.GramDefs.token
      list -> Aut.GramDefs.parse_tree_list -> (Aut.Gram.production, tuple)
      sigT option -> 'a1) -> hole_future_invariant -> 'a1
    
    val hole_future_invariant_rec :
      bool -> ((Aut.Gram.symbol list, tuple) sigT -> __ -> Aut.GramDefs.token
      list -> Aut.GramDefs.parse_tree_list -> (Aut.Gram.production, tuple)
      sigT option -> 'a1) -> hole_future_invariant -> 'a1
    
    val future_hfi :
      bool -> hole_future_invariant -> (Aut.Gram.symbol list, tuple) sigT
    
    val word_future_hfi :
      bool -> hole_future_invariant -> Aut.GramDefs.token list
    
    val future_sem_proof_hfi :
      bool -> hole_future_invariant -> Aut.GramDefs.parse_tree_list
    
    val hole_hfi :
      bool -> hole_future_invariant -> (Aut.Gram.production, tuple) sigT
      option
    
    val hole_pseudo_hfi :
      bool -> hole_future_invariant -> (Aut.Gram.production option, tuple)
      sigT option
    
    val symbl_hfi : bool -> hole_future_invariant -> Aut.Gram.symbol list
    
    val sem_hfi : bool -> hole_future_invariant -> tuple
    
    val coq_JMeq_rew_r : 'a1 -> 'a2 -> 'a3 -> 'a3
    
    val eq_rew_r_dep : 'a1 -> 'a1 -> 'a2 -> 'a2
    
    val eq_rew_dep : 'a1 -> 'a2 -> 'a1 -> 'a2
   end
  
  val complete_validator : bool
  
  val safe_validator : bool
  
  val parse : nat -> Aut.GramDefs.token coq_Stream -> Inter.parse_result
 end

val parse : nat -> Aut.GramDefs.token coq_Stream -> Parser.Inter.parse_result

