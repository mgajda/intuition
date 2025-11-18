#!/usr/bin/env python3
"""
Simple TPTP to DIMACS CNF converter for propositional logic
Uses Tseitin transformation to convert arbitrary propositional formulas to CNF
"""

import re
import sys
from collections import defaultdict

class TPTPtoCNF:
    def __init__(self):
        self.var_counter = 1
        self.var_map = {}
        self.clauses = []

    def get_var(self, name):
        """Get or create variable number for a propositional variable"""
        if name not in self.var_map:
            self.var_map[name] = self.var_counter
            self.var_counter += 1
        return self.var_map[name]

    def new_var(self):
        """Create a fresh auxiliary variable"""
        v = self.var_counter
        self.var_counter += 1
        return v

    def parse_formula(self, formula_str):
        """Parse simple TPTP propositional formula"""
        # Remove whitespace
        f = formula_str.replace(' ', '').replace('\n', '')
        return self.convert_to_cnf(f)

    def convert_to_cnf(self, formula):
        """Convert formula to CNF using Tseitin transformation"""
        # For now, handle simple cases manually
        # This is a simplified converter for the test formulas

        # Parse the formula and build expression tree
        expr, root_var = self.parse_expr(formula)

        # Assert that the root is true
        self.clauses.append([root_var])

        return self.clauses

    def parse_expr(self, s):
        """Parse expression and return (expr_str, tseitin_var)"""
        s = s.strip()

        # Handle negation
        if s.startswith('~'):
            inner_expr, inner_var = self.parse_expr(s[1:])
            result_var = self.new_var()
            # result_var <=> ~inner_var
            # (~result_var | ~inner_var) & (result_var | inner_var)
            self.clauses.append([-result_var, -inner_var])
            self.clauses.append([result_var, inner_var])
            return s, result_var

        # Handle parentheses
        if s.startswith('(') and s.endswith(')'):
            return self.parse_expr(s[1:-1])

        # Find main connective (implication has lowest precedence)
        # Look for => outside of parentheses
        depth = 0
        for i in range(len(s)-1, -1, -1):
            if s[i] == ')':
                depth += 1
            elif s[i] == '(':
                depth -= 1
            elif depth == 0 and s[i:i+2] == '=>':
                left, left_var = self.parse_expr(s[:i])
                right, right_var = self.parse_expr(s[i+2:])
                result_var = self.new_var()
                # result_var <=> (left_var => right_var)
                # result_var <=> (~left_var | right_var)
                # (~result_var | ~left_var | right_var) & (result_var | left_var) & (result_var | ~right_var)
                self.clauses.append([-result_var, -left_var, right_var])
                self.clauses.append([result_var, left_var])
                self.clauses.append([result_var, -right_var])
                return s, result_var

        # Look for | (or) - lower precedence than &
        depth = 0
        for i in range(len(s)-1, -1, -1):
            if s[i] == ')':
                depth += 1
            elif s[i] == '(':
                depth -= 1
            elif depth == 0 and s[i] == '|':
                left, left_var = self.parse_expr(s[:i])
                right, right_var = self.parse_expr(s[i+1:])
                result_var = self.new_var()
                # result_var <=> (left_var | right_var)
                # (~result_var | left_var | right_var) & (result_var | ~left_var) & (result_var | ~right_var)
                self.clauses.append([-result_var, left_var, right_var])
                self.clauses.append([result_var, -left_var])
                self.clauses.append([result_var, -right_var])
                return s, result_var

        # Look for & (and)
        depth = 0
        for i in range(len(s)-1, -1, -1):
            if s[i] == ')':
                depth += 1
            elif s[i] == '(':
                depth -= 1
            elif depth == 0 and s[i] == '&':
                left, left_var = self.parse_expr(s[:i])
                right, right_var = self.parse_expr(s[i+1:])
                result_var = self.new_var()
                # result_var <=> (left_var & right_var)
                # (~result_var | left_var) & (~result_var | right_var) & (result_var | ~left_var | ~right_var)
                self.clauses.append([-result_var, left_var])
                self.clauses.append([-result_var, right_var])
                self.clauses.append([result_var, -left_var, -right_var])
                return s, result_var

        # Must be a propositional variable
        var = self.get_var(s)
        return s, var

    def to_dimacs(self):
        """Convert to DIMACS CNF format"""
        num_vars = self.var_counter - 1
        num_clauses = len(self.clauses)

        result = [f"p cnf {num_vars} {num_clauses}"]
        for clause in self.clauses:
            result.append(' '.join(map(str, clause)) + ' 0')
        return '\n'.join(result)

def convert_tptp_file(input_file, output_file):
    """Convert a TPTP file to DIMACS CNF"""
    with open(input_file, 'r') as f:
        content = f.read()

    # Extract the formula from fof(..., conjecture, (...))
    match = re.search(r'fof\([^,]+,\s*conjecture\s*,\s*\(([^)]+)\)\)', content, re.DOTALL)
    if not match:
        print(f"Could not extract formula from {input_file}")
        return False

    formula = match.group(1)
    print(f"Formula: {formula}")

    converter = TPTPtoCNF()
    try:
        converter.parse_formula(formula)
        dimacs = converter.to_dimacs()

        with open(output_file, 'w') as f:
            f.write(f"c Converted from {input_file}\n")
            f.write(f"c Formula: {formula}\n")
            f.write(dimacs + '\n')

        print(f"Converted to {output_file}")
        return True
    except Exception as e:
        print(f"Error converting {input_file}: {e}")
        import traceback
        traceback.print_exc()
        return False

if __name__ == '__main__':
    if len(sys.argv) != 3:
        print("Usage: tptp_to_cnf.py <input.p> <output.cnf>")
        sys.exit(1)

    input_file = sys.argv[1]
    output_file = sys.argv[2]

    if convert_tptp_file(input_file, output_file):
        sys.exit(0)
    else:
        sys.exit(1)
