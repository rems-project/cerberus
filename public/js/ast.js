CodeMirror.defineMode("ast", (config, modeConfig) => {

  let whiteCharRE = /[ \t\v\f]/
  var largeRE = /[A-Z]/;
  let idRE = /[a-z_A-Z0-9'\xa1-\uffff]/;
  var digitRE = /\d/;
  var hexitRE = /[0-9A-Fa-f]/;
  var octitRE = /[0-7]/;

  let keywords = {}
  function setType(t) {
    return function () {
      for (var i = 0; i < arguments.length; i++)
        keywords[arguments[i]] = t;
    };
  }

  setType("declarator")(
    // Cabs
    "TUnit", "EDecl_func", "Declarator", "DDecl_function", "DDecl_identifier",
    "Params",
    // Ail
    "AilSigma", "AilDeclarations", "Decl_function"
  )

  setType("definition")(
    // Cabs
    "FunDef", "Specifiers", "Type_specifiers", "TSpec_int",
    "None", "Some", "List",
    // Ail
    "AilTagDefinitions", "AilObjectDefinitions", "AilFunctionDefinitions",
    "STD", "Bindings", "EMPTY"
  )

  function switchState (source, setState, f) {
    setState(f);
    return f(source, setState);
  }

  function normal(stream, setState) {
    if (stream.eatWhile(whiteCharRE))
      return null

    let ch = stream.next()

    // Tree delimiter
    if (ch == '`' || ch == '|' || ch == '-')
      return "builtin"

    // String literal
    if (ch == '"') {
      return switchState(stream, setState, stringLiteral);
    }

    // Types enclosed by '
    if (ch == '\'') {
      return switchState(stream, setState, typeLiteral);
    }

    // Location enclosed by < and >
    if (ch == '<') {
      return switchState(stream, setState, location);
    }

    // Numbers
    if (digitRE.test(ch)) {
      if (ch == '0') {
        if (stream.eat(/[xX]/)) {
          stream.eatWhile(hexitRE); // should require at least 1
          return "integer";
        }
        if (stream.eat(/[oO]/)) {
          stream.eatWhile(octitRE); // should require at least 1
          return "number";
        }
      }
      stream.eatWhile(digitRE);
      var t = "number";
      if (stream.match(/^\.\d+/)) {
        t = "number";
      }
      if (stream.eat(/[eE]/)) {
        t = "number";
        stream.eat(/[-+]/);
        stream.eatWhile(digitRE); // should require at least 1
      }
      return t;
    }

    // Keywords
    if (largeRE.test(ch)) {
      stream.eatWhile(idRE)
      let w = stream.current()
      return keywords[w] ? keywords[w] : "ast-constructor"
    }

    // Variables
    if (idRE.test(ch)) {
      stream.eatWhile(idRE)
      return "variable-2"
    }

    return null
  }

  function typeLiteral(source, setState) {
    while (!source.eol()) {
      var ch = source.next();
      if (ch == '\'') {
        setState(normal);
        return "type";
      }
      if (ch == '\\') {
        if (source.eol() || source.eat(whiteCharRE)) {
          setState(stringGap);
          return "type";
        }
        if (source.eat('&')) {
        }
        else {
          source.next(); // should handle other escapes here
        }
      }
    }
    setState(normal);
    return "string error";
  }

  function location(source, setState) {
    while (!source.eol()) {
      var ch = source.next();
      if (ch == '>') {
        setState(normal);
        return "line";
      }
      if (ch == '\\') {
        if (source.eol() || source.eat(whiteCharRE)) {
          setState(stringGap);
          return "line";
        }
        if (source.eat('&')) {
        }
        else {
          source.next(); // should handle other escapes here
        }
      }
    }
    setState(normal);
    return "string error";
  }

  function stringLiteral(source, setState) {
    while (!source.eol()) {
      var ch = source.next();
      if (ch == '"') {
        setState(normal);
        return "string";
      }
      if (ch == '\\') {
        if (source.eol() || source.eat(whiteCharRE)) {
          setState(stringGap);
          return "string";
        }
        if (source.eat('&')) {
        }
        else {
          source.next(); // should handle other escapes here
        }
      }
    }
    setState(normal);
    return "string error";
  }

  return {
    startState: () => { return { f: normal } },
    copyState: (s) => { return { f: s.f } },
    token: (stream, state) => {
      return state.f(stream, (g) => state.f = g)
    },
    blockCommendStart: "{-",
    blockCommentEnd:   "-}",
    lineComment:       "--"
  }

})

CodeMirror.defineMIME("text/x-ast-dump", "ast")
