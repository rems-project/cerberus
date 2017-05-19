// NB> use TextEncoder here, on web
/*
function f(str) {
  var encoder = new TextEncoder();
  return encoder.encode(str);
}
*/
function f(str) {
  var out = [], p = 0;
  for (var i = 0; i < str.length; i++) {
    var c = str.charCodeAt(i);
    if (c < 128) {
      out[p++] = c;
    } else if (c < 2048) {
      out[p++] = (c >> 6) | 192;
      out[p++] = (c & 63) | 128;
    } else if (
        ((c & 0xFC00) == 0xD800) && (i + 1) < str.length &&
        ((str.charCodeAt(i + 1) & 0xFC00) == 0xDC00)) {
      // Surrogate Pair
      c = 0x10000 + ((c & 0x03FF) << 10) + (str.charCodeAt(++i) & 0x03FF);
      out[p++] = (c >> 18) | 240;
      out[p++] = ((c >> 12) & 63) | 128;
      out[p++] = ((c >> 6) & 63) | 128;
      out[p++] = (c & 63) | 128;
    } else {
      out[p++] = (c >> 12) | 224;
      out[p++] = ((c >> 6) & 63) | 128;
      out[p++] = (c & 63) | 128;
    }
  }
  return out;
};

// Wrapper function for main - input = name of input source file - output = name of output source file (in virtual directory)
function callMain(args) {
  var argc = args.length+1;
  function pad() {
    for (var i = 0; i < 4-1; i++) {
      argv.push(0);
    }
  }
  var argv = [allocate(intArrayFromString(Module['thisProgram']), 'i8', ALLOC_NORMAL) ];
  pad();
  for (var i = 0; i < argc-1; i = i + 1) {
    argv.push(allocate(intArrayFromString(args[i]), 'i8', ALLOC_NORMAL));
    pad();
  }
  argv.push(0);
  argv = allocate(argv, 'i32', ALLOC_NORMAL);

  Module["_mcpp_lib_main"](argc, argv);
}

function invoke_cpp_standard_args(input, output) {
  callMain(["-N", "-I-", "-I", "/include/c/libc", "-I", "/include/c/posix", input, output])
}

function printFile(name) {
  var read = FS.readFile(name, {encoding: "utf8"});
  console.log(read);
}

var data = f("int main() {return 0;}\n");
var stream = FS.open('test1.c', 'w+');
FS.write(stream, data, 0, data.length, 0);
FS.close(stream);
invoke_cpp_standard_args("test1.c", "test1-cpp.c");
printFile("test1-cpp.c")

/*
// define a dummy stdio
FS.mkdir('/include');
FS.mkdir('/include/c');
FS.mkdir('/include/c/libc');
var data = f("\n");
var stream = FS.open('/include/c/libc/stdio.h', 'w+');
FS.write(stream, data, 0, data.length, 0);
FS.close(stream);

var data = f("#include <stdio.h>\nint main() {return 0;}\n");
var stream = FS.open('test2.c', 'w+');
FS.write(stream, data, 0, data.length, 0);
FS.close(stream);
// note: unless stdio is loaded into virtual file system, this will cause an error.
invoke_cpp_standard_args("test2.c", "test2-cpp.c");
printFile("test2-cpp.c")

*/
