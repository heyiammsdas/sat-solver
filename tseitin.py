import sys
import re

class Var:
    def __init__(self, name): self.name = name
class UnOp:
    def __init__(self, op, child): self.op, self.child = op, child
class BinOp:
    def __init__(self, op, left, right): self.op, self.left, self.right = op, left, right

def tokenize(text):
    token_specification = [
        ('EQUIV',  r'<->'),
        ('IMPL',   r'->'),
        ('AND',    r'&'),
        ('OR',     r'\|'),
        ('NOT',    r'~'),
        ('LPAREN', r'\('),
        ('RPAREN', r'\)'),
        ('VAR',    r'[A-Za-z_][A-Za-z0-9_]*'),
        ('SKIP',   r'[ \t\n\r]+'),
        ('MISMATCH', r'.'),
    ]
    tok_regex = '|'.join('(?P<%s>%s)' % pair for pair in token_specification)
    tokens = []
    for mo in re.finditer(tok_regex, text):
        kind = mo.lastgroup
        value = mo.group()
        if kind == 'SKIP': continue
        if kind == 'MISMATCH': raise ValueError(f"Unexpected character: '{value}'")
        tokens.append((kind, value))
    return tokens

class Parser:
    def __init__(self, tokens):
        self.tokens = tokens
        self.pos = 0

    def match(self, *expected_kinds):
        if self.pos < len(self.tokens) and self.tokens[self.pos][0] in expected_kinds:
            kind = self.tokens[self.pos][0]
            self.pos += 1
            return kind
        return None

    def parse(self):
        if not self.tokens:
            raise ValueError("Empty formula")
        node = self.parse_equiv()
        if self.pos < len(self.tokens):
            raise ValueError(f"Unexpected token at end: {self.tokens[self.pos][1]}")
        return node

    def parse_equiv(self):
        node = self.parse_impl()
        while self.match('EQUIV'):
            node = BinOp('<->', node, self.parse_impl())
        return node

    def parse_impl(self):
        node = self.parse_or()
        while self.match('IMPL'):
            node = BinOp('->', node, self.parse_or())
        return node

    def parse_or(self):
        node = self.parse_and()
        while self.match('OR'):
            node = BinOp('|', node, self.parse_and())
        return node

    def parse_and(self):
        node = self.parse_primary()
        while self.match('AND'):
            node = BinOp('&', node, self.parse_primary())
        return node

    def parse_primary(self):
        if self.match('NOT'):
            return UnOp('~', self.parse_primary())
        elif self.match('LPAREN'):
            node = self.parse_equiv()
            if not self.match('RPAREN'):
                raise ValueError("Missing closing parenthesis")
            return node
        else:
            if self.pos < len(self.tokens) and self.tokens[self.pos][0] == 'VAR':
                var_name = self.tokens[self.pos][1]
                self.pos += 1
                return Var(var_name)
            raise ValueError("Expected a variable or '('")

class Tseitin:
    def __init__(self):
        self.var_map = {}
        self.next_id = 1
        self.clauses = []

    def get_id(self, name=None):
        if name is not None:
            if name not in self.var_map:
                self.var_map[name] = self.next_id
                self.next_id += 1
            return self.var_map[name]
        else:
            fresh = self.next_id
            self.next_id += 1
            return fresh

    def transform(self, node):
        if isinstance(node, Var):
            return self.get_id(node.name)
            
        elif isinstance(node, UnOp):
            child_id = self.transform(node.child)
            my_id = self.get_id()
            self.clauses.append([-my_id, -child_id])
            self.clauses.append([my_id, child_id])
            return my_id
            
        elif isinstance(node, BinOp):
            left_id = self.transform(node.left)
            right_id = self.transform(node.right)
            my_id = self.get_id()
            
            if node.op == '&':
                self.clauses.append([-my_id, left_id])
                self.clauses.append([-my_id, right_id])
                self.clauses.append([my_id, -left_id, -right_id])
            elif node.op == '|':
                self.clauses.append([my_id, -left_id])
                self.clauses.append([my_id, -right_id])
                self.clauses.append([-my_id, left_id, right_id])
            elif node.op == '->':
                self.clauses.append([my_id, left_id])
                self.clauses.append([my_id, -right_id])
                self.clauses.append([-my_id, -left_id, right_id])
            elif node.op == '<->':
                self.clauses.append([-my_id, -left_id, right_id])
                self.clauses.append([-my_id, left_id, -right_id])
                self.clauses.append([my_id, left_id, right_id])
                self.clauses.append([my_id, -left_id, -right_id])
            return my_id

def main():
    if len(sys.argv) != 3:
        print("Usage: python tseitin.py <input.txt> <output.cnf>")
        sys.exit(1)

    input_file = sys.argv[1]
    output_file = sys.argv[2]

    try:
        with open(input_file, 'r') as f:
            formula_text = f.read().strip()
    except FileNotFoundError:
        print(f"Error: Could not find input file '{input_file}'")
        sys.exit(1)

    tokens = tokenize(formula_text)
    
    parser = Parser(tokens)
    ast = parser.parse()
    
    transformer = Tseitin()
    root_id = transformer.transform(ast)
    
    transformer.clauses.append([root_id])
    
    num_vars = transformer.next_id - 1
    num_clauses = len(transformer.clauses)
    
    with open(output_file, 'w') as f:
        f.write(f"c Tseitin transformation of: {formula_text}\n")
        f.write("c Variable Mapping:\n")
        for var_name, var_id in transformer.var_map.items():
            f.write(f"c {var_id} -> {var_name}\n")
        f.write(f"p cnf {num_vars} {num_clauses}\n")
        for clause in transformer.clauses:
            f.write(" ".join(map(str, clause)) + " 0\n")
            
    print(f"Success! Translated formula to {num_vars} variables and {num_clauses} clauses in '{output_file}'")

if __name__ == "__main__":
    main()