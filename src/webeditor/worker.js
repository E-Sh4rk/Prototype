importScripts("typechecker.js");
onmessage = function(e) {
    const res = JSON.parse(checker.typecheck(e.data, (res) => postMessage([JSON.parse(res), false])));
    postMessage([res, true]);
  }