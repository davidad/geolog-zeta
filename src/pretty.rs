//! Pretty-printer for Geolog AST
//!
//! Renders AST back to source syntax for round-trip testing.

use crate::ast::*;

/// Pretty-print configuration
pub struct PrettyConfig {
    pub indent: usize,
}

impl Default for PrettyConfig {
    fn default() -> Self {
        Self { indent: 2 }
    }
}

/// A pretty-printer with indentation tracking
pub struct Pretty {
    output: String,
    indent_level: usize,
    config: PrettyConfig,
}

impl Default for Pretty {
    fn default() -> Self {
        Self::new()
    }
}

impl Pretty {
    pub fn new() -> Self {
        Self {
            output: String::new(),
            indent_level: 0,
            config: PrettyConfig::default(),
        }
    }

    pub fn finish(self) -> String {
        self.output
    }

    fn indent(&mut self) {
        for _ in 0..(self.indent_level * self.config.indent) {
            self.output.push(' ');
        }
    }

    fn write(&mut self, s: &str) {
        self.output.push_str(s);
    }

    fn writeln(&mut self, s: &str) {
        self.output.push_str(s);
        self.output.push('\n');
    }

    fn newline(&mut self) {
        self.output.push('\n');
    }

    fn inc_indent(&mut self) {
        self.indent_level += 1;
    }

    fn dec_indent(&mut self) {
        self.indent_level = self.indent_level.saturating_sub(1);
    }
}

// ============ Pretty-printing implementations ============

impl Pretty {
    pub fn file(&mut self, file: &File) {
        for (i, decl) in file.declarations.iter().enumerate() {
            if i > 0 {
                self.newline();
            }
            self.declaration(&decl.node);
        }
    }

    pub fn declaration(&mut self, decl: &Declaration) {
        match decl {
            Declaration::Namespace(name) => {
                self.write("namespace ");
                self.write(name);
                self.writeln(";");
            }
            Declaration::Theory(t) => self.theory_decl(t),
            Declaration::Instance(i) => self.instance_decl(i),
            Declaration::Query(q) => self.query_decl(q),
        }
    }

    pub fn theory_decl(&mut self, t: &TheoryDecl) {
        self.write("theory ");
        for param in &t.params {
            self.write("(");
            self.write(&param.name);
            self.write(" : ");
            self.type_expr(&param.ty);
            self.write(") ");
        }
        self.write(&t.name);
        self.writeln(" {");
        self.inc_indent();
        for item in &t.body {
            self.indent();
            self.theory_item(&item.node);
            self.newline();
        }
        self.dec_indent();
        self.writeln("}");
    }

    pub fn theory_item(&mut self, item: &TheoryItem) {
        match item {
            TheoryItem::Sort(name) => {
                self.write(name);
                self.write(" : Sort;");
            }
            TheoryItem::Function(f) => {
                self.write(&f.name.to_string());
                self.write(" : ");
                self.type_expr(&f.domain);
                self.write(" -> ");
                self.type_expr(&f.codomain);
                self.write(";");
            }
            TheoryItem::Axiom(a) => self.axiom_decl(a),
            TheoryItem::Field(name, ty) => {
                self.write(name);
                self.write(" : ");
                self.type_expr(ty);
                self.write(";");
            }
        }
    }

    pub fn axiom_decl(&mut self, a: &AxiomDecl) {
        self.write(&a.name.to_string());
        self.write(" : forall ");
        for (i, qv) in a.quantified.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            self.write(&qv.names.join(", "));
            self.write(" : ");
            self.type_expr(&qv.ty);
        }
        self.write(". ");

        // Hypotheses (if any)
        if !a.hypotheses.is_empty() {
            for (i, hyp) in a.hypotheses.iter().enumerate() {
                if i > 0 {
                    self.write(", ");
                }
                self.formula(hyp);
            }
            self.write(" ");
        }

        self.write("|- ");
        self.formula(&a.conclusion);
        self.write(";");
    }

    pub fn type_expr(&mut self, ty: &TypeExpr) {
        match ty {
            TypeExpr::Sort => self.write("Sort"),
            TypeExpr::Prop => self.write("Prop"),
            TypeExpr::Path(p) => self.write(&p.to_string()),
            TypeExpr::App(f, a) => {
                self.type_expr(f);
                self.write(" ");
                self.type_expr_atom(a);
            }
            TypeExpr::Arrow(d, c) => {
                self.type_expr_atom(d);
                self.write(" -> ");
                self.type_expr(c);
            }
            TypeExpr::Record(fields) => {
                self.write("[");
                for (i, (name, ty)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(name);
                    self.write(" : ");
                    self.type_expr(ty);
                }
                self.write("]");
            }
            TypeExpr::Instance(t) => {
                self.type_expr(t);
                self.write(" instance");
            }
        }
    }

    /// Print a type expression that might need parentheses
    fn type_expr_atom(&mut self, ty: &TypeExpr) {
        match ty {
            TypeExpr::Arrow(_, _) | TypeExpr::App(_, _) => {
                self.write("(");
                self.type_expr(ty);
                self.write(")");
            }
            _ => self.type_expr(ty),
        }
    }

    pub fn term(&mut self, t: &Term) {
        match t {
            Term::Path(p) => self.write(&p.to_string()),
            Term::App(f, a) => {
                self.term(f);
                self.write(" ");
                self.term_atom(a);
            }
            Term::Project(t, field) => {
                self.term(t);
                self.write(" .");
                self.write(field);
            }
            Term::Record(fields) => {
                self.write("[");
                for (i, (name, val)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(name);
                    self.write(": ");
                    self.term(val);
                }
                self.write("]");
            }
        }
    }

    /// Print a term that might need parentheses
    fn term_atom(&mut self, t: &Term) {
        match t {
            Term::App(_, _) | Term::Project(_, _) => {
                self.write("(");
                self.term(t);
                self.write(")");
            }
            _ => self.term(t),
        }
    }

    pub fn formula(&mut self, f: &Formula) {
        match f {
            Formula::True => self.write("true"),
            Formula::False => self.write("false"),
            Formula::RelApp(rel_name, arg) => {
                // Postfix relation application: term rel
                self.term(arg);
                self.write(" ");
                self.write(rel_name);
            }
            Formula::Eq(l, r) => {
                self.term(l);
                self.write(" = ");
                self.term(r);
            }
            Formula::And(conjuncts) => {
                for (i, c) in conjuncts.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.formula(c);
                }
            }
            Formula::Or(disjuncts) => {
                for (i, d) in disjuncts.iter().enumerate() {
                    if i > 0 {
                        self.write(" \\/ ");
                    }
                    self.formula_atom(d);
                }
            }
            Formula::Exists(vars, body) => {
                self.write("(exists ");
                for (i, qv) in vars.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(&qv.names.join(", "));
                    self.write(" : ");
                    self.type_expr(&qv.ty);
                }
                self.write(". ");
                self.formula(body);
                self.write(")");
            }
        }
    }

    /// Print a formula that might need parentheses
    fn formula_atom(&mut self, f: &Formula) {
        match f {
            Formula::Or(_) | Formula::And(_) => {
                self.write("(");
                self.formula(f);
                self.write(")");
            }
            _ => self.formula(f),
        }
    }

    pub fn instance_decl(&mut self, i: &InstanceDecl) {
        self.write("instance ");
        self.write(&i.name);
        self.write(" : ");
        self.type_expr(&i.theory);
        self.writeln(" = {");
        self.inc_indent();
        for item in &i.body {
            self.indent();
            self.instance_item(&item.node);
            self.newline();
        }
        self.dec_indent();
        self.writeln("}");
    }

    pub fn instance_item(&mut self, item: &InstanceItem) {
        match item {
            InstanceItem::Element(name, ty) => {
                self.write(name);
                self.write(" : ");
                self.type_expr(ty);
                self.write(";");
            }
            InstanceItem::Equation(lhs, rhs) => {
                self.term(lhs);
                self.write(" = ");
                self.term(rhs);
                self.write(";");
            }
            InstanceItem::NestedInstance(name, inner) => {
                self.write(name);
                self.writeln(" = {");
                self.inc_indent();
                for item in &inner.body {
                    self.indent();
                    self.instance_item(&item.node);
                    self.newline();
                }
                self.dec_indent();
                self.indent();
                self.write("};");
            }
            InstanceItem::RelationAssertion(term, rel) => {
                self.term(term);
                self.write(" ");
                self.write(rel);
                self.write(";");
            }
        }
    }

    pub fn query_decl(&mut self, q: &QueryDecl) {
        self.write("query ");
        self.write(&q.name);
        self.writeln(" {");
        self.inc_indent();
        self.indent();
        self.write("? : ");
        self.type_expr(&q.goal);
        self.writeln(";");
        self.dec_indent();
        self.writeln("}");
    }
}

/// Convenience function to pretty-print a file
pub fn pretty_print(file: &File) -> String {
    let mut p = Pretty::new();
    p.file(file);
    p.finish()
}

// Unit tests moved to tests/unit_pretty.rs
