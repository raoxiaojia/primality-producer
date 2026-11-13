//! Parses the input number, a decimal numeral or an expression over numerals with `+`, `-`, `*`,
//! `^` and parentheses. An expression is evaluated as Lean evaluates it in `ℕ` and printed back as
//! the Lean term the certificates state.

use num_traits::{CheckedSub, ToPrimitive};

use crate::arith::{self, BigUint};

/// The largest value, in bits, of a numeral in an expression and of every intermediate result.
pub const MAX_BITS: u64 = 10_000;
/// The largest exponent of `^`, whatever the base.
pub const MAX_EXPONENT: u32 = 10_000;
/// The most tokens an expression may have. It bounds the depth of the parse tree, and with it
/// the recursion of the parser, the printer and the tree's drop.
pub const MAX_TOKENS: usize = 400;

/// A numeral or expression longer than this many digits is shown shortened in error messages.
const BRIEF_DIGITS: usize = 20;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Input {
    /// The value.
    pub n: BigUint,
    /// The value as a Lean argument term: the numeral, or the expression in parentheses
    /// (`(2 ^ 255 - 19)`).
    pub term: String,
    /// The largest exponent of a `^` in the expression (`None` without one).
    pub max_exponent: Option<u32>,
}

/// Parses `text`, whose value may have at most `max_digits` digits. A text of digits and
/// whitespace alone is one numeral with the whitespace ignored (a wrapped paste). In an
/// expression whitespace separates tokens. A subtraction below zero is an error, since Lean's
/// `ℕ` subtraction would give 0, and so is an input past the `MAX_*` limits.
pub fn parse_input(text: &str, max_digits: usize) -> Result<Input, String> {
    let text = text.trim();
    if text.is_empty() {
        return Err("the input is empty".to_string());
    }
    if text
        .chars()
        .all(|c| c.is_ascii_digit() || c.is_whitespace())
    {
        let digits: String = text.chars().filter(char::is_ascii_digit).collect();
        if digits.len() > max_digits {
            return Err(format!(
                "the input has {} digits, more than the {max_digits} allowed",
                digits.len()
            ));
        }
        let n = BigUint::parse_bytes(digits.as_bytes(), 10).expect("a run of digits parses");
        return Ok(Input {
            term: n.to_string(),
            n,
            max_exponent: None,
        });
    }
    let mut parser = Parser {
        tokens: tokenize(text)?,
        position: 0,
    };
    let expr = parser.sum()?;
    match parser.peek() {
        Token::End => {}
        Token::Op(')') => return Err("the input has an unmatched `)`".to_string()),
        token => {
            return Err(format!(
                "expected an operator or the end of the input, found {}",
                describe(token)
            ))
        }
    }
    let digits = arith::digits(&expr.value);
    if digits > max_digits {
        return Err(format!(
            "the value has {digits} digits, more than the {max_digits} allowed"
        ));
    }
    let term = match expr.node {
        Node::Num => expr.value.to_string(),
        _ => format!("({})", lean_text(&expr)),
    };
    let max_exponent = max_exponent(&expr);
    Ok(Input {
        n: expr.value,
        term,
        max_exponent,
    })
}

/// Parses a printed `Input::term` back. The outer parentheses of an expression's term are
/// stripped first, since they would take an input at `MAX_TOKENS` past the limit. The result
/// must print back to `term` exactly, so that a caller stating `term` states what it checked.
pub fn parse_term(term: &str) -> Result<Input, String> {
    let inner = term
        .strip_prefix('(')
        .and_then(|rest| rest.strip_suffix(')'))
        .unwrap_or(term);
    let input = parse_input(inner, usize::MAX)?;
    if input.term != term {
        return Err(format!("the term {term} prints back as {}", input.term));
    }
    Ok(input)
}

/// The largest exponent of a `^` in `expr`.
fn max_exponent(expr: &Expr) -> Option<u32> {
    match &expr.node {
        Node::Num => None,
        Node::Bin(op, left, right) => {
            let own = (*op == Op::Pow).then(|| right.value.to_u32().expect("a checked exponent"));
            [own, max_exponent(left), max_exponent(right)]
                .into_iter()
                .flatten()
                .max()
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Token {
    Num(BigUint),
    Op(char),
    End,
}

/// The tokens of `text`, ending in `Token::End`.
fn tokenize(text: &str) -> Result<Vec<Token>, String> {
    let mut tokens = Vec::new();
    let mut chars = text.char_indices().peekable();
    while let Some((start, c)) = chars.next() {
        if c.is_whitespace() {
            continue;
        }
        if tokens.len() == MAX_TOKENS {
            return Err(format!("the expression has more than {MAX_TOKENS} tokens"));
        }
        if c.is_ascii_digit() {
            let mut end = start + 1;
            while let Some(&(i, d)) = chars.peek() {
                if !d.is_ascii_digit() {
                    break;
                }
                end = i + 1;
                chars.next();
            }
            let digits = &text[start..end];
            // A numeral of more digits than this has more than `MAX_BITS` bits, and is
            // rejected before it is parsed.
            let max_numeral_digits = (MAX_BITS as f64 * std::f64::consts::LOG10_2).ceil() as usize;
            let value = (digits.len() <= max_numeral_digits)
                .then(|| BigUint::parse_bytes(digits.as_bytes(), 10).expect("digits parse"))
                .filter(|value| value.bits() <= MAX_BITS)
                .ok_or_else(|| {
                    format!(
                        "the number {} has more than {MAX_BITS} bits",
                        brief_text(digits)
                    )
                })?;
            tokens.push(Token::Num(value));
        } else if "+-*^()".contains(c) {
            tokens.push(Token::Op(c));
        } else {
            return Err(format!(
                "the input contains `{c}`, which is neither a digit nor one of `+ - * ^ ( )`"
            ));
        }
    }
    tokens.push(Token::End);
    Ok(tokens)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Op {
    Add,
    Sub,
    Mul,
    Pow,
}

impl Op {
    fn symbol(self) -> char {
        match self {
            Op::Add => '+',
            Op::Sub => '-',
            Op::Mul => '*',
            Op::Pow => '^',
        }
    }

    /// Lean's precedence of the operator.
    fn precedence(self) -> u32 {
        match self {
            Op::Add | Op::Sub => 65,
            Op::Mul => 70,
            Op::Pow => 75,
        }
    }
}

#[derive(Clone, Debug)]
enum Node {
    Num,
    Bin(Op, Box<Expr>, Box<Expr>),
}

/// A parsed subexpression with its value.
#[derive(Clone, Debug)]
struct Expr {
    node: Node,
    value: BigUint,
}

impl Expr {
    /// The precedence of the subexpression's head; a numeral binds tightest.
    fn precedence(&self) -> u32 {
        match &self.node {
            Node::Num => u32::MAX,
            Node::Bin(op, _, _) => op.precedence(),
        }
    }
}

/// A recursive-descent parser over the tokens, evaluating as it goes.
struct Parser {
    tokens: Vec<Token>,
    position: usize,
}

impl Parser {
    fn peek(&self) -> &Token {
        &self.tokens[self.position]
    }

    fn next(&mut self) -> Token {
        let token = self.tokens[self.position].clone();
        if token != Token::End {
            self.position += 1;
        }
        token
    }

    /// `sum := product (("+" | "-") product)*`, left-associative.
    fn sum(&mut self) -> Result<Expr, String> {
        let mut left = self.product()?;
        while let Token::Op(c @ ('+' | '-')) = *self.peek() {
            self.next();
            let right = self.product()?;
            left = combine(if c == '+' { Op::Add } else { Op::Sub }, left, right)?;
        }
        Ok(left)
    }

    /// `product := power ("*" power)*`, left-associative.
    fn product(&mut self) -> Result<Expr, String> {
        let mut left = self.power()?;
        while *self.peek() == Token::Op('*') {
            self.next();
            let right = self.power()?;
            left = combine(Op::Mul, left, right)?;
        }
        Ok(left)
    }

    /// `power := atom ("^" power)?`, right-associative.
    fn power(&mut self) -> Result<Expr, String> {
        let base = self.atom()?;
        if *self.peek() != Token::Op('^') {
            return Ok(base);
        }
        self.next();
        let exponent = self.power()?;
        combine(Op::Pow, base, exponent)
    }

    /// `atom := numeral | "(" sum ")"`.
    fn atom(&mut self) -> Result<Expr, String> {
        match self.next() {
            Token::Num(value) => Ok(Expr {
                node: Node::Num,
                value,
            }),
            Token::Op('(') => {
                let inner = self.sum()?;
                match self.next() {
                    Token::Op(')') => Ok(inner),
                    token => Err(format!("expected `)`, found {}", describe(&token))),
                }
            }
            token => Err(format!(
                "expected a number or `(`, found {}",
                describe(&token)
            )),
        }
    }
}

/// `left op right`, evaluated in `ℕ` within the limits.
fn combine(op: Op, left: Expr, right: Expr) -> Result<Expr, String> {
    let (a, b) = (&left.value, &right.value);
    let value = match op {
        Op::Add => a + b,
        Op::Sub => a.checked_sub(b).ok_or_else(|| {
            format!(
                "the subtraction {} - {} goes below zero",
                brief(a),
                brief(b)
            )
        })?,
        Op::Mul => a * b,
        Op::Pow => {
            let exponent = b
                .to_u32()
                .filter(|&e| e <= MAX_EXPONENT)
                .ok_or_else(|| format!("the exponent {} is above {MAX_EXPONENT}", brief(b)))?;
            // When `a ≥ 2`, `a ^ e` has between `(bits(a) - 1) · e + 1` and `bits(a) · e` bits.
            // So a power that passes this check has fewer than `MAX_BITS + e` bits.
            if a.bits() >= 2 && (a.bits() - 1) * u64::from(exponent) + 1 > MAX_BITS {
                return Err(too_large(op, a, b));
            }
            // `0 ^ 0 = 1`, as in Lean.
            a.pow(exponent)
        }
    };
    if value.bits() > MAX_BITS {
        return Err(too_large(op, a, b));
    }
    Ok(Expr {
        node: Node::Bin(op, Box::new(left), Box::new(right)),
        value,
    })
}

fn too_large(op: Op, a: &BigUint, b: &BigUint) -> String {
    format!(
        "{} {} {} has more than {MAX_BITS} bits",
        brief(a),
        op.symbol(),
        brief(b)
    )
}

/// The expression in Lean syntax, with spaces around each operator and only the parentheses Lean
/// needs to read the same tree back (`+`, `-` and `*` associate to the left, `^` to the right).
fn lean_text(expr: &Expr) -> String {
    match &expr.node {
        Node::Num => expr.value.to_string(),
        Node::Bin(op, left, right) => {
            let p = op.precedence();
            let right_assoc = *op == Op::Pow;
            let wrap = |child: &Expr, parens: bool| {
                if parens {
                    format!("({})", lean_text(child))
                } else {
                    lean_text(child)
                }
            };
            let left_text = wrap(
                left,
                left.precedence() < p || (right_assoc && left.precedence() == p),
            );
            let right_text = wrap(
                right,
                right.precedence() < p || (!right_assoc && right.precedence() == p),
            );
            format!("{left_text} {} {right_text}", op.symbol())
        }
    }
}

fn describe(token: &Token) -> String {
    match token {
        Token::Num(value) => format!("the number {}", brief(value)),
        Token::Op(c) => format!("`{c}`"),
        Token::End => "the end of the input".to_string(),
    }
}

fn brief(value: &BigUint) -> String {
    brief_text(&value.to_string())
}

/// The decimal `digits` in full when short, else its first digits and its length.
fn brief_text(digits: &str) -> String {
    if digits.len() <= BRIEF_DIGITS {
        digits.to_string()
    } else {
        format!("{}… ({} digits)", &digits[..8], digits.len())
    }
}

#[cfg(test)]
mod tests {
    use num_traits::One;

    use super::*;

    fn big(s: &str) -> BigUint {
        BigUint::parse_bytes(s.as_bytes(), 10).unwrap()
    }

    fn parse(text: &str) -> Result<Input, String> {
        parse_input(text, 2000)
    }

    fn term(text: &str) -> String {
        parse(text).unwrap().term
    }

    fn error(text: &str) -> String {
        parse(text).unwrap_err()
    }

    #[test]
    fn a_numeral_ignores_whitespace_and_leading_zeros() {
        let input = parse(" 1000\n003 ").unwrap();
        assert_eq!(input.n, big("1000003"));
        assert_eq!(input.term, "1000003");
        assert_eq!(term("007"), "7");
    }

    #[test]
    fn a_numeral_over_the_digit_limit_is_rejected() {
        assert_eq!(
            parse_input("1234", 3).unwrap_err(),
            "the input has 4 digits, more than the 3 allowed"
        );
    }

    #[test]
    fn expressions_evaluate_with_lean_precedence() {
        let input = parse("2^255 - 19").unwrap();
        assert_eq!(input.n, (BigUint::one() << 255usize) - BigUint::from(19u32));
        assert_eq!(input.term, "(2 ^ 255 - 19)");
        assert_eq!(parse("5*2^5947+1").unwrap().term, "(5 * 2 ^ 5947 + 1)");
        assert_eq!(parse("2^3^2").unwrap().n, BigUint::from(512u32));
        assert_eq!(parse("10 - 3 - 2").unwrap().n, BigUint::from(5u32));
        assert_eq!(parse("(7)").unwrap().term, "7");
        assert_eq!(parse("0^0 + 1").unwrap().n, BigUint::from(2u32));
    }

    #[test]
    fn a_printed_term_parses_back_to_itself() {
        for text in ["1000003", "2^255 - 19", "10 - (3 - 2)", "(2 ^ 3) ^ 2"] {
            let input = parse(text).unwrap();
            assert_eq!(parse_term(&input.term), Ok(input));
        }
        assert_eq!(
            parse_term("(2^255 - 19)").unwrap_err(),
            "the term (2^255 - 19) prints back as (2 ^ 255 - 19)"
        );
        assert!(parse_term("(1) + (2)").is_err());
    }

    #[test]
    fn the_largest_exponent_is_reported() {
        assert_eq!(parse("1000003").unwrap().max_exponent, None);
        assert_eq!(parse("1000000 + 3").unwrap().max_exponent, None);
        assert_eq!(parse("2^255 - 19").unwrap().max_exponent, Some(255));
        assert_eq!(
            parse("2^256 - 2^224 + 2^9 - 1").unwrap().max_exponent,
            Some(256)
        );
        // The exponent of `2 ^ 3 ^ 2` is the value 9 of `3 ^ 2`.
        assert_eq!(parse("2 ^ 3 ^ 2").unwrap().max_exponent, Some(9));
        assert_eq!(parse("7 ^ 0 + 2").unwrap().max_exponent, Some(0));
    }

    #[test]
    fn parentheses_are_kept_where_lean_needs_them() {
        assert_eq!(term("10 - (3 - 2)"), "(10 - (3 - 2))");
        assert_eq!(term("10 - (3 + 2)"), "(10 - (3 + 2))");
        assert_eq!(term("(10 - 3) + 2"), "(10 - 3 + 2)");
        // In `ℕ`, `a + (b - c)` and `a + b - c` differ, so the tree is kept.
        assert_eq!(term("1 + (5 - 3)"), "(1 + (5 - 3))");
        assert_eq!(term("2 * (3 * 4)"), "(2 * (3 * 4))");
        assert_eq!(term("(2 ^ 3) ^ 2"), "((2 ^ 3) ^ 2)");
        assert_eq!(term("2 ^ (3 ^ 2)"), "(2 ^ 3 ^ 2)");
        assert_eq!(term("(2 + 3) * 4"), "((2 + 3) * 4)");
        assert_eq!(term("(2 * 3) ^ 2 + 1"), "((2 * 3) ^ 2 + 1)");
    }

    #[test]
    fn syntax_errors_name_the_problem() {
        assert_eq!(error(""), "the input is empty");
        assert_eq!(
            error("2^x"),
            "the input contains `x`, which is neither a digit nor one of `+ - * ^ ( )`"
        );
        assert_eq!(
            error("2^"),
            "expected a number or `(`, found the end of the input"
        );
        assert_eq!(error("*3"), "expected a number or `(`, found `*`");
        assert_eq!(error("-3 + 5"), "expected a number or `(`, found `-`");
        assert_eq!(error("(2 + 3"), "expected `)`, found the end of the input");
        assert_eq!(error("2 + 3)"), "the input has an unmatched `)`");
        assert_eq!(
            error("2^12 7"),
            "expected an operator or the end of the input, found the number 7"
        );
    }

    #[test]
    fn values_below_zero_are_rejected() {
        assert_eq!(error("3 - 5 + 10"), "the subtraction 3 - 5 goes below zero");
        // A negative exponent cannot arise either.
        assert_eq!(
            error("2 ^ (1 - 2)"),
            "the subtraction 1 - 2 goes below zero"
        );
    }

    #[test]
    fn sizes_are_bounded_at_every_step() {
        assert_eq!(error("2 ^ 10001"), "the exponent 10001 is above 10000");
        assert_eq!(error("1 ^ 100000"), "the exponent 100000 is above 10000");
        assert_eq!(error("2 ^ 10000"), "2 ^ 10000 has more than 10000 bits");
        assert_eq!(
            error("2 ^ 9999 - 2 ^ 9998"),
            "the value has 3010 digits, more than the 2000 allowed"
        );
        assert_eq!(
            error("2 ^ 9999 * 2 - 1"),
            format!(
                "{} * 2 has more than 10000 bits",
                brief(&(BigUint::one() << 9999usize))
            )
        );
        // An intermediate result may exceed the digit limit as long as the value does not.
        let input = parse("2 ^ 7000 - (2 ^ 7000 - 7)").unwrap();
        assert_eq!(input.n, BigUint::from(7u32));
        let numeral = "9".repeat(3011);
        assert_eq!(
            error(&format!("{numeral} + 1")),
            "the number 99999999… (3011 digits) has more than 10000 bits"
        );
        // The token limit bounds both a long chain and deep nesting.
        let chain = vec!["1"; 200].join("+");
        assert_eq!(parse(&chain).unwrap().n, BigUint::from(200u32));
        assert_eq!(
            error(&format!("{chain}+1")),
            "the expression has more than 400 tokens"
        );
        let deep = format!("{}1{}", "(".repeat(199), ")".repeat(199));
        assert_eq!(parse(&deep).unwrap().term, "1");
        assert_eq!(
            error(&format!("({deep})")),
            "the expression has more than 400 tokens"
        );
        assert_eq!(
            parse_input("10 ^ 5", 5).unwrap_err(),
            "the value has 6 digits, more than the 5 allowed"
        );
    }
}
