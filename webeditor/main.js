requirejs.config({baseUrl: '.', paths: { vs: 'node_modules/monaco-editor/min/vs' }});
requirejs(['vs/editor/editor.main','cookie'], function () {

	let theme = getCookie("theme");
	if (!theme) theme = "vs-custom-dark";
	function updateTheme() {
		let r = document.querySelector(':root');
		if (theme == "vs-custom") {
			r.style.setProperty('--modal-background', '#e1e1e1');
			r.style.setProperty('--modal-color', '#333');
			r.style.setProperty('--modal-hover', '#bbb');
			r.style.setProperty('--overlay-color', '#333');
			r.style.setProperty('--overlay-a-color', '#222');
			r.style.setProperty('--overlay-version', '#008000');
			r.style.setProperty('--overlay-shortcut', '#b8860b');
			r.style.setProperty('--overlay-background', '#e1e1e1');
		}
		else {
			r.style.setProperty('--modal-background', '#1e1e1e');
			r.style.setProperty('--modal-color', '#ccc');
			r.style.setProperty('--modal-hover', '#444');
			r.style.setProperty('--overlay-color', '#ccc');
			r.style.setProperty('--overlay-a-color', '#ddd');
			r.style.setProperty('--overlay-version', '#008000');
			r.style.setProperty('--overlay-shortcut', '#9acd32');
			r.style.setProperty('--overlay-background', '#1e1e1e');
		}
		monaco.editor.setTheme(theme);
		setCookie("theme", theme, 90);
	}

	monaco.languages.register({ id: 'stml' });
	monaco.editor.defineTheme('vs-custom-dark', {
		base: 'vs-dark',
		inherit: true,
		rules: [
			// { token: 'identifier.term', foreground: 'DCDCAA' },
			{ token: 'identifier.type', foreground: 'DD5555' },
			{ token: 'identifier.vartype', foreground: 'DD7777' },
		],
		colors: {
			"editorCodeLens.foreground": "#AAAAAA",
		}	
	});
	monaco.editor.defineTheme('vs-custom', {
		base: 'vs',
		inherit: true,
		rules: [
			// { token: 'identifier.term', foreground: 'DCDCAA' },
			{ token: 'identifier.type', foreground: '991111' },
			{ token: 'identifier.vartype', foreground: '993333' },
		],
		colors: {
			"editorCodeLens.foreground": "#333333",
		}	
	});
	let editor = monaco.editor.create(document.getElementById('container'), {
		value: '(* Press F2 to load an example. *)\n(* Press Ctrl-Enter to type the current buffer. *)\n(* (also accessible via context menu) *)\n\n',
		theme: theme,
		language: 'stml',
		automaticLayout: true,
		minimap: { enabled: false }
	});
	editor.focus();
	updateTheme();

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

	// Action to switch theme
	requirejs([], function () {
		editor.addAction({
			id: 'theme',
			label: 'Switch dark/light theme',
			keybindings: [monaco.KeyCode.F4],
			precondition: null,
			keybindingContext: null,
			contextMenuGroupId: 'operation',
			contextMenuOrder: 1.5,
			run: () => {
				if (theme == "vs-custom-dark")
					theme = "vs-custom";
				else
					theme = "vs-custom-dark";
				updateTheme();
			}
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
			label: 'Type current buffer',
			keybindings: [monaco.KeyMod.CtrlCmd | monaco.KeyCode.Enter],
			precondition: null,
			keybindingContext: null,
			contextMenuGroupId: 'operation',
			contextMenuOrder: 1.5,
			run: typecheck
		});
})});
