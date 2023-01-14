requirejs.config({baseUrl: '.', paths: { vs: 'node_modules/monaco-editor/min/vs' }});
requirejs(['vs/editor/editor.main'], function () {

	monaco.languages.register({ id: 'stml' });
	monaco.editor.defineTheme('vs-custom', {
		base: 'vs-dark',
		inherit: true,
		rules: [
			// { token: 'identifier.term', foreground: 'DCDCAA' },
			{ token: 'identifier.type', foreground: 'DD5555' },
			{ token: 'identifier.vartype', foreground: 'DD7777' },
		],
		colors: {

		}	
	});
	let editor = monaco.editor.create(document.getElementById('container'), {
		value: '(* Press CTRL+Enter to typecheck the program. *)\n(* Press F2 to load an example. *)\n\n',
		theme: 'vs-custom',
		language: 'stml',
		automaticLayout: true,
		minimap: { enabled: false },
		'bracketPairColorization.enabled': false // TODO
		// Temporary... until the brackets colorization is fixed
		// https://github.com/microsoft/monaco-editor/issues/3449
	});
	editor.focus();

	// Register tokenizer
	requirejs(['tokenizer'], function () {
		monaco.languages.setMonarchTokensProvider('stml', getTokenizer());
	});
	let model = editor.getModel();

	// Configure language
	const config = {
		comments: { blockComment: ["(*", "*)"] },
		brackets: [['{', '}'],['[', ']'],['(', ')']],
		colorizedBracketPairs: [['{', '}'],['[', ']'],['(', ')']],
		surroundingPairs: [
		  { open: '{', close: '}' },
		  { open: '[', close: ']' },
		  { open: '(', close: ')' },
		  { open: '<', close: '>' },
		  { open: "'", close: "'" },
		  { open: '"', close: '"' },
		],
		autoClosingPairs: [
		  { open: '{', close: '}' },
		  { open: '[', close: ']' },
		  { open: '(', close: ')' },
		  { open: '"', close: '"', notIn: ['string', 'comment'] },
		],
	  };
	monaco.languages.setLanguageConfiguration('stml', config);

	// Action to load examples
	requirejs(['load'], function () {
		function loadContent(content) {
			if (content !== null) {
				model.setValue(content);
			}
			editor.focus();
		}
		editor.addAction({
			id: 'load',
			label: 'Load an example',
			keybindings: [monaco.KeyCode.F2],
			precondition: null,
			keybindingContext: null,
			contextMenuGroupId: 'operation',
			contextMenuOrder: 1.5,
			run: () => showLoadModal(loadContent)
		});
	});
	
	// Register codelens and the typechecker
	requirejs(['codelens'], function () {
		// Register codelens
		monaco.languages.registerCodeLensProvider('stml', getCodeLens(editor, model));
		// Register the typechecking action
		let lock = false;
		let changes = [];
		model.onDidChangeContent((e) => { if (lock) changes.push(...e.changes); });
		const messageContribution = editor.getContribution('editor.contrib.messageController');
		function treatResult(res) {
			if (res["exit_code"] < 0) {
				let pos = editor.getPosition();
				if (res["pos"].length > 0) {
					let range = applyChangesToRange(res["pos"][0]["startOffset"], res["pos"][0]["endOffset"], changes);
					if (range !== null)
						pos = model.getPositionAt(range[0]);
				}
				messageContribution.showMessage(res["message"], pos);
			}
			else {
				updateCodeLens(res["results"], changes);
			}
		}
		function initNewWorker() {
			try {
				if (!window.Worker) return null;
				let worker = new Worker("worker.js");
				worker.onmessage = function(e) {
					treatResult(e.data[0]);
					if (e.data[1])
						lock = false;
				}
				return worker;
			}
			catch (e) { }
			return null;
		}
		let worker = initNewWorker();
		function typecheck() {
			changes = [];
			if (worker !== null) {
				if (lock) {
					worker.terminate();
					worker = initNewWorker();
				}
				lock = true;
				clearCodeLens();
				worker.postMessage(model.getValue());
			} else {
				requirejs(['typechecker'], function () {
					treatResult(JSON.parse(checker.typecheck(model.getValue(), null)));
				});
			}
		}
		editor.addAction({
			id: 'typecheck',
			label: 'Typecheck program',
			keybindings: [monaco.KeyMod.CtrlCmd | monaco.KeyCode.Enter],
			precondition: null,
			keybindingContext: null,
			contextMenuGroupId: 'operation',
			contextMenuOrder: 1.5,
			run: typecheck
		});
})});