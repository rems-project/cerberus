/**
 * NOTE: These functions rely on mcpp.js being loaded first
 */

/**
 * This function relies of TextEncoder from the browser
 **/
function encodeText(str) {
  var encoder = new TextEncoder();
  return encoder.encode(str);
}

function saveFile(name, str) {
  var data = encodeText(str);
  var stream = FS.open(name, 'w+');
  FS.write(stream, data, 0, data.length, 0);
  FS.close(stream);
}

function readFile(name) {
  return FS.readFile(name, {encoding: 'utf8'});
}

function setupFS() {
  FS.mkdir('/include');
  FS.mkdir('/include/c');
  FS.mkdir('/include/c/libc');
  FS.mkdir('/include/c/posix');
}

function invokeCpp(content) {
  function call(args) {
    var argc = args.length+1;
    function pad() {
      for (var i = 0; i < 4-1; i++) {
        argv.push(0);
      }
    }
    var argv =
      [allocate(intArrayFromString(Module['thisProgram']), 'i8', ALLOC_NORMAL)];
    pad();
    for (var i = 0; i < argc-1; i = i + 1) {
      argv.push(allocate(intArrayFromString(args[i]), 'i8', ALLOC_NORMAL));
      pad();
    }
    argv.push(0);
    argv = allocate(argv, 'i32', ALLOC_NORMAL);

    Module["_mcpp_lib_main"](argc, argv);
  }
  var input = "buffer.c";
  var output = "buffer.cpp";
  var data = encodeText(content);
  var stream = FS.open("buffer.c", "w");
  FS.write(stream, data, 0, data.length, 0);
  FS.close(stream);
  call(['-N', '-I-', '-I', '/include/c/libc', '-I', '/include/c/posix',
    input, output])
  return caml_new_string(readFile(output));
}
