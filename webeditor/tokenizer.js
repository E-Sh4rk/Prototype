function getTokenizer() {
    return {
        defaultToken: '',
        tokenPostfix: '.stml',
    
        keywords: [
            'atoms', 'atom', 'type', 'where', 'and', 'if', 'is', 'then',
            'else', 'match', 'with', 'end', 'fun', 'let', 'in',
            'fst', 'snd',  'magic', 'true', 'false',
            'nil', 'unit', 'rec', 'gen'
        ],

        typeids: [
            'Any', 'Empty', 'Bool', 'Char', 'Int', 'Float',
            'Unit', 'True', 'False', 'String', 'List'
        ],
    
        operators: [
            '||', '->', '&', '|', '\\', '~', ':',
            '=', '=?', '?', ';', '*', '--', '::',
            '..', '-', '+', '/'
        ],

        delimiters: /[;,\.]/,
    
        // we include these common regular expressions
        symbols: /[=><!~?:&|+\-*\/\^%]+/,
        // escapes: /\\(?:[abfnrtv\\"']|x[0-9A-Fa-f]{1,4}|u[0-9A-Fa-f]{4}|U[0-9A-Fa-f]{8})/,
        digits: /\d+(_+\d+)*/,
        octaldigits: /[0-7]+(_+[0-7]+)*/,
        binarydigits: /[0-1]+(_+[0-1]+)*/,
        hexdigits: /[[0-9a-fA-F]+(_+[0-9a-fA-F]+)*/,
    
        // The main tokenizer for our language
        tokenizer: {
            root: [
                // identifiers and keywords
                [/[a-z_][\w']*/, {
                    cases: {
                        '@keywords': { token: 'keyword.$0' },
                        '@default': 'identifier.term'
                    }
                }],
                [/[A-Z][\w']*/, 'identifier.type'],
    
                // whitespace
                { include: '@whitespace' },
    
                // delimiters and operators
                [/[{}()\[\]]/, '@brackets'],
                [/[<>](?!@symbols)/, '@brackets'],
                [/@symbols/, {
                    cases: {
                        '@operators': 'delimiter',
                        '@default': ''
                    }
                }],

                // numbers
                // [/(@digits)[eE]([\-+]?(@digits))?[fFdD]?/, 'number.float'],
                // [/(@digits)\.(@digits)([eE][\-+]?(@digits))?[fFdD]?/, 'number.float'],
                // [/0[xX](@hexdigits)[Ll]?/, 'number.hex'],
                // [/0(@octaldigits)[Ll]?/, 'number.octal'],
                // [/0[bB](@binarydigits)[Ll]?/, 'number.binary'],
                // [/(@digits)[fFdD]/, 'number.float'],
                // [/(@digits)[lL]?/, 'number'],
                [/(@digits)[eE]([\-+]?(@digits))?/, 'number.float'],
                [/(@digits)\.(@digits)([eE][\-+]?(@digits))?/, 'number.float'],
                [/(@digits)/, 'number'],
    
                // delimiters: after number because of .\d floats
                [/@delimiters/, 'delimiter'],
    
                // strings
                [/"([^"])*$/, 'string.invalid'], // [/"([^"\\]|\\.)*$/, 'string.invalid'],  // non-teminated string
                [/"/, 'string', '@string'],
    
                // characters
                [/'[^']'/, 'string'],// [/'[^\\']'/, 'string'],
                // [/(')(@escapes)(')/, ['string', 'string.escape', 'string']],
                // [/'/, 'string.invalid']

                // type var identifier
                [/'[\w]+/, 'identifier.vartype'],
                [/'/, 'string.invalid']
            ],
    
            whitespace: [
                [/[ \t\r\n]+/, ''],
                [/\(\*/, 'comment', '@comment'],
            ],
    
            comment: [
                [/[^\(*]+/, 'comment'],
                [/\(\*/, 'comment', '@push' ],
                [/\*\)/, 'comment', '@pop'],
                [/[\(*]/, 'comment']
            ],
    
            string: [
                [/[^"]+/, 'string'], // [/[^\\"]+/, 'string'],
                // [/@escapes/, 'string.escape'],
                // [/\\./, 'string.escape.invalid'],
                [/"/, 'string', '@pop']
            ],
        },
    };    
}