type ('spec, 'res) t = {
    spec_name : Sym.t;
    spec : 'spec;
    resolved : 'res option
  }
