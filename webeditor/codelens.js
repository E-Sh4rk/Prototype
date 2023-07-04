function applyChangesToRange(startL, endL, changes) {
    for (let i = 0; i < changes.length; i++) {
        let c = changes[i];
        let start = c.rangeOffset;
        let end = start + c.rangeLength;
        let diff = c.text.length - c.rangeLength;
        if (startL >= end) {
            startL += diff;
            endL += diff;
        }
        else if (endL <= start) { }
        else {
            return null;
        }
    }
    return [startL, endL];
}

let codelensemitter = new monaco.Emitter();
let typesinfo = [];
function applyChangesToCurCodeLens(changes) {
    for (let i = 0; i < typesinfo.length; i++) {
        let startL = typesinfo[i]["def_pos"]["startOffset"];
        let endL = typesinfo[i]["def_pos"]["endOffset"];
        let range = applyChangesToRange(startL, endL, changes);
        if (range === null) {
            typesinfo.splice(i,1);
            i--;
        }
        else {
            typesinfo[i]["def_pos"]["startOffset"] = range[0];
            typesinfo[i]["def_pos"]["endOffset"] = range[1];
        }
    }
}
function updateCodeLens(types, changes) {
    typesinfo = types;
    applyChangesToCurCodeLens(changes);
    codelensemitter.fire();
}
function clearCodeLens() {
    updateCodeLens([], []);
}

function getCodeLens(editor, model) {
    model.onDidChangeContent((e) => { applyChangesToCurCodeLens(e.changes); });
    function rangeOfPositions(start, end) {
        return  {
                    startLineNumber: start.lineNumber,
                    startColumn: start.column,
                    endLineNumber: end.lineNumber,
                    endColumn: end.column
				};
    }
    let copyCmd = editor.addCommand(0, function(ctx, ...arguments) {navigator.clipboard.writeText(arguments[0])});
    return {
        onDidChange: codelensemitter.event,
        provideCodeLenses: function (model, token) {
            let lenses = typesinfo.map(info => {
                let start = model.getPositionAt(info["def_pos"]["startOffset"]);
                let end = model.getPositionAt(info["def_pos"]["endOffset"]);
                let range = rangeOfPositions(start, end);
                let name = info["name"];
                if (info["typeable"]) {
                    let tooltip = "Inferred in "+Math.round(info["time"])+"ms\nClick to copy the type";
                    let type = info["type"];
                    return {range: range, id: name, command: {id: copyCmd, title: type, arguments: [type], tooltip: tooltip}}
                }
                else {
                    let tooltip = "Inferred in "+Math.round(info["time"])+"ms";
                    let msg = "Untypeable: "+info["message"];
                    return {range: range, id: name, command: {id: copyCmd, title: msg, arguments: [msg], tooltip: tooltip}}
                }
            });
            return {
                lenses: lenses,
                dispose: () => {}
            };
        },
        resolveCodeLens: function (model, codeLens, token) {
            return codeLens;
        }
    };
}