import type { ReactElement } from 'react';
import { BOARD, STROKE } from '../../contract/tokens';
import { Box, DIAGRAM_VIEWBOX, Label, Line, MONO_TITLE, reveal } from './diagram';
import { Stepper, type Step } from './stepper';

/**
 * Tier 3 — the Pratt parser, tracing `browser/vjs-syntax` (crate J3).
 *
 * Every annotation names something real in the crate:
 *
 * - the token kinds are `vjs_syntax::TokenKind` (`token.rs`);
 * - the binding powers are the `(op, l_bp, r_bp)` triples returned by
 *   `match_binary_op` (`parser.rs`);
 * - the climb is `parse_binary_expr(p, fuel, min_bp, allow_in)`, entered with
 *   `min_bp = 0` from `parse_conditional_expr`;
 * - the tree is `ExprKind::Binary { op, left, right }` over the arena;
 * - the guard is `DiagnosticKind::UnparenthesizedNullishAndLogicalMix`.
 *
 * The source program is `a || b && c`: two operators, two different binding
 * powers, and one precedence decision that the AST has to get right.
 */

/** The program traced by the scene. */
const SOURCE = 'a || b && c';

/** One token of the trace, named after the crate's own enum variants. */
interface PrattToken {
  /** `TokenKind` variant. */
  kind: string;
  /** The token text. */
  text: string;
  /** The `Punctuator` variant, when the token is a punctuator. */
  variant?: string;
}

/** The token stream `tokenize` produces for {@link SOURCE}. */
const TOKENS: readonly PrattToken[] = [
  { kind: 'TokenKind::Ident', text: 'a' },
  { kind: 'TokenKind::Punct', text: '||', variant: 'Punctuator::PipePipe' },
  { kind: 'TokenKind::Ident', text: 'b' },
  { kind: 'TokenKind::Punct', text: '&&', variant: 'Punctuator::AmpAmp' },
  { kind: 'TokenKind::Ident', text: 'c' },
  { kind: 'TokenKind::Eof', text: 'EOF' },
];

/** One row of the `match_binary_op` table. */
interface BindingPowerRow {
  token: string;
  op: string;
  left: number;
  right: number;
}

/**
 * The binding powers the crate assigns to the two operators in the trace.
 * Values are taken verbatim from `match_binary_op` in
 * `browser/vjs-syntax/src/parser.rs`.
 */
const BINDING_POWERS: readonly BindingPowerRow[] = [
  { token: '||', op: 'BinOp::LogicalOr', left: 4, right: 5 },
  { token: '&&', op: 'BinOp::LogicalAnd', left: 6, right: 7 },
];

const CELL_WIDTH = 96;
const CELL_GAP = 18;

/** Draw the token stream as a row of hairline cells. */
function TokenRow(props: {
  tokens: readonly PrattToken[];
  t: number;
  failing?: readonly string[];
}): ReactElement {
  const { tokens, t, failing = [] } = props;
  const total = tokens.length * CELL_WIDTH + (tokens.length - 1) * CELL_GAP;
  const origin = (720 - total) / 2;
  return (
    <g>
      {tokens.map((token, index) => {
        const x = origin + index * (CELL_WIDTH + CELL_GAP);
        const progress = reveal(t, index, tokens.length);
        const isFailing = failing.includes(token.text);
        return (
          <g key={`${token.kind}-${index}`} opacity={progress}>
            <Label
              x={x + CELL_WIDTH / 2}
              y={96}
              anchor="middle"
              color={BOARD.rib}
              size={8}
            >
              {token.kind}
            </Label>
            <Box
              x={x}
              y={106}
              w={CELL_WIDTH}
              h={44}
              stroke={isFailing ? BOARD.fail : BOARD.line}
              progress={progress}
            />
            <Label
              x={x + CELL_WIDTH / 2}
              y={134}
              anchor="middle"
              color={isFailing ? BOARD.fail : BOARD.live}
              size={13}
              weight={600}
            >
              {token.text}
            </Label>
            {token.variant === undefined ? null : (
              <Label
                x={x + CELL_WIDTH / 2}
                y={164}
                anchor="middle"
                color={BOARD.rib}
                size={8}
              >
                {token.variant}
              </Label>
            )}
          </g>
        );
      })}
    </g>
  );
}

/** The scene header: what is being traced, and over which source. */
function SceneHeader(props: { title: string; source?: string }): ReactElement {
  return (
    <g>
      <Label x={20} y={26} color={BOARD.inkHi} size={11} weight={600}>
        {props.title}
      </Label>
      <Label x={700} y={26} anchor="end" color={BOARD.rib}>
        {props.source === undefined ? 'VJS_SYNTAX — J3' : `SOURCE: ${props.source}`}
      </Label>
      <Line x1={20} y1={38} x2={700} y2={38} stroke={BOARD.rib} strokeWidth={STROKE.hatch} />
    </g>
  );
}

/** Step 1 — the token stream. */
function TokenStreamStep(props: { t: number }): ReactElement {
  return (
    <svg
      viewBox={DIAGRAM_VIEWBOX}
      className="stage-diagram"
      role="img"
      aria-label="Token stream produced by the vjs_syntax lexer"
      preserveAspectRatio="xMidYMid meet"
    >
      <SceneHeader title="1 · TOKEN STREAM" source={SOURCE} />
      <TokenRow tokens={TOKENS} t={props.t} />
      <Label x={20} y={205} color={BOARD.ink} size={9}>
        TOKENIZE RETURNS 5 EXECUTABLE TOKENS + EOF — THE PARSER NEVER READS THE SOURCE AGAIN.
      </Label>
      <Label x={20} y={228} color={BOARD.rib} size={9}>
        {'TOKEN { KIND, SPAN, PRECEDED_BY_LINE_TERMINATOR }'}
      </Label>
      <Label x={20} y={251} color={BOARD.rib} size={9}>
        TRIVIA — WHITESPACE §12.2, LINE TERMINATORS §12.3, COMMENTS §12.4 — IS SKIPPED, NOT TOKENIZED.
      </Label>
      <Label x={20} y={274} color={BOARD.rib} size={9}>
        PUNCTUATORS ARE SCANNED LONGEST-MATCH FIRST, §12.8.1.
      </Label>
    </svg>
  );
}

/** Step 2 — the binding powers. */
function BindingPowerStep(props: { t: number }): ReactElement {
  const rows = BINDING_POWERS;
  const headerY = 82;
  const rowHeight = 34;
  return (
    <svg
      viewBox={DIAGRAM_VIEWBOX}
      className="stage-diagram"
      role="img"
      aria-label="Binding powers assigned to the logical operators"
      preserveAspectRatio="xMidYMid meet"
    >
      <SceneHeader title="2 · BINDING POWERS" source={SOURCE} />
      <Label x={150} y={headerY} color={BOARD.rib} size={8}>
        TOKEN
      </Label>
      <Label x={230} y={headerY} color={BOARD.rib} size={8}>
        OP
      </Label>
      <Label x={470} y={headerY} color={BOARD.rib} size={8}>
        L_BP
      </Label>
      <Label x={550} y={headerY} color={BOARD.rib} size={8}>
        R_BP
      </Label>
      <Line x1={130} y1={headerY + 8} x2={600} y2={headerY + 8} stroke={BOARD.rib} strokeWidth={STROKE.hatch} />
      {rows.map((row, index) => {
        const y = headerY + 30 + index * rowHeight;
        const progress = reveal(props.t, index, rows.length);
        return (
          <g key={row.token} opacity={progress}>
            <Line
              x1={130}
              y1={y + 22}
              x2={600}
              y2={y + 22}
              stroke={BOARD.rib}
              strokeWidth={STROKE.hatch}
              progress={progress}
            />
            <Label x={150} y={y + 12} color={BOARD.live} size={12} weight={600}>
              {row.token}
            </Label>
            <Label x={230} y={y + 12} color={BOARD.ink} size={9}>
              {row.op}
            </Label>
            <Label x={470} y={y + 12} color={BOARD.accent} size={12} weight={600}>
              {row.left}
            </Label>
            <Label x={550} y={y + 12} color={BOARD.accent} size={12} weight={600}>
              {row.right}
            </Label>
          </g>
        );
      })}
      <Label x={130} y={200} color={BOARD.ink} size={9}>
        MATCH_BINARY_OP RETURNS (OP, L_BP, R_BP) FOR ALL 24 LEFT-ASSOCIATIVE BINARY OPERATORS.
      </Label>
      <Label x={130} y={223} color={BOARD.rib} size={9}>
        PROVED: OP ≠ BINOP::EXP ∧ L_BP &lt; R_BP ∧ R_BP ≤ 23.
      </Label>
      <Label x={130} y={246} color={BOARD.rib} size={9}>
        L_BP &lt; R_BP MAKES EVERY BINARY OPERATOR LEFT-ASSOCIATIVE; THE RIGHT SIDE IS CLIMBED AT R_BP.
      </Label>
    </svg>
  );
}

/** Step 3 — precedence climbing. */
function PrecedenceClimbStep(props: { t: number }): ReactElement {
  const frames = [
    {
      title: 'parse_binary_expr(min_bp = 0)',
      body: 'SEES || — L_BP 4 ≥ 0 — CONSUME, CLIMB RIGHT AT min_bp = 5',
    },
    {
      title: 'parse_binary_expr(min_bp = 5)',
      body: 'SEES && — L_BP 6 ≥ 5 — CONSUME, CLIMB RIGHT AT min_bp = 7',
    },
    {
      title: 'parse_binary_expr(min_bp = 7)',
      body: 'SEES EOF — NO OPERATOR — RETURN c',
    },
  ];
  return (
    <svg
      viewBox={DIAGRAM_VIEWBOX}
      className="stage-diagram"
      role="img"
      aria-label="Precedence climbing through parse_binary_expr"
      preserveAspectRatio="xMidYMid meet"
    >
      <SceneHeader title="3 · PRECEDENCE CLIMBING" source={SOURCE} />
      {frames.map((frame, index) => {
        const progress = reveal(props.t, index, frames.length);
        const x = 60 + index * 30;
        const y = 66 + index * 62;
        const w = 600 - index * 60;
        return (
          <g key={frame.title} opacity={progress}>
            <Box x={x} y={y} w={w} h={48} progress={progress} />
            <Label x={x + 14} y={y + 20} color={BOARD.live} size={10} weight={600}>
              {frame.title}
            </Label>
            <Label x={x + 14} y={y + 38} color={BOARD.ink} size={9}>
              {frame.body}
            </Label>
          </g>
        );
      })}
      <Label x={60} y={262} color={BOARD.ink} size={9}>
        LEFT OPERAND IS PARSED FIRST, THEN THE OPERATOR IS MATCHED, THEN THE RIGHT SIDE IS CLIMBED.
      </Label>
      <Label x={60} y={285} color={BOARD.rib} size={9}>
        THE LOOP STOPS WHEN THE NEXT OPERATOR HAS L_BP &lt; min_bp — HERE, EOF HAS NO OPERATOR AT ALL.
      </Label>
    </svg>
  );
}

/** One node of the AST diagram. */
function AstNode(props: {
  x: number;
  y: number;
  w: number;
  text: string;
  t: number;
  fill?: string;
}): ReactElement {
  const { x, y, w, text, t, fill } = props;
  return (
    <g opacity={t}>
      <Box x={x} y={y} w={w} h={26} stroke={fill ?? BOARD.line} progress={t} />
      <Label x={x + w / 2} y={y + 18} anchor="middle" color={fill ?? BOARD.live} size={11} weight={600}>
        {text}
      </Label>
    </g>
  );
}

/** Step 4 — the AST. */
function AstStep(props: { t: number }): ReactElement {
  const nodes = [
    { x: 328, y: 58, w: 64, text: '||' },
    { x: 148, y: 132, w: 56, text: 'a' },
    { x: 428, y: 132, w: 64, text: '&&' },
    { x: 356, y: 206, w: 56, text: 'b' },
    { x: 486, y: 206, w: 56, text: 'c' },
  ];
  const progress = (index: number): number => reveal(props.t, index, nodes.length + 1);
  return (
    <svg
      viewBox={DIAGRAM_VIEWBOX}
      className="stage-diagram"
      role="img"
      aria-label="Abstract syntax tree produced by the parser"
      preserveAspectRatio="xMidYMid meet"
    >
      <SceneHeader title="4 · AST" source={SOURCE} />
      <g opacity={progress(0)}>
        <Line x1={360} y1={84} x2={360} y2={108} progress={progress(0)} />
        <Line x1={176} y1={108} x2={360} y2={108} progress={progress(0)} />
        <Line x1={360} y1={108} x2={460} y2={108} progress={progress(0)} />
        <Line x1={176} y1={108} x2={176} y2={132} progress={progress(0)} />
        <Line x1={460} y1={108} x2={460} y2={132} progress={progress(0)} />
      </g>
      <g opacity={progress(1)}>
        <Line x1={460} y1={158} x2={460} y2={182} progress={progress(1)} />
        <Line x1={384} y1={182} x2={460} y2={182} progress={progress(1)} />
        <Line x1={460} y1={182} x2={514} y2={182} progress={progress(1)} />
        <Line x1={384} y1={182} x2={384} y2={206} progress={progress(1)} />
        <Line x1={514} y1={182} x2={514} y2={206} progress={progress(1)} />
      </g>
      {nodes.map((node, index) => (
        <AstNode
          key={node.text}
          x={node.x}
          y={node.y}
          w={node.w}
          text={node.text}
          t={progress(index + 1)}
        />
      ))}
      <Label x={20} y={248} color={BOARD.ink} size={9}>
        {'ExprKind::Binary { op: BinOp::LogicalOr, left: Ident("a"),'}
      </Label>
      <Label x={20} y={264} color={BOARD.ink} size={9}>
        {'  right: ExprKind::Binary { op: BinOp::LogicalAnd, left: Ident("b"), right: Ident("c") } }'}
      </Label>
      <Label x={20} y={280} color={BOARD.rib} size={9}>
        {'IDENT("a") IS EXPRKIND::IDENT(IDENT { NAME: "a" }).'}
      </Label>
    </svg>
  );
}

/** Step 5 — the §13.13 early error. */
function EarlyErrorStep(props: { t: number }): ReactElement {
  const failing = ['??', '||'];
  const tokens: readonly PrattToken[] = [
    { kind: 'TokenKind::Ident', text: 'a' },
    { kind: 'TokenKind::Punct', text: '??', variant: 'Punctuator::QuestionQuestion' },
    { kind: 'TokenKind::Ident', text: 'b' },
    { kind: 'TokenKind::Punct', text: '||', variant: 'Punctuator::PipePipe' },
    { kind: 'TokenKind::Ident', text: 'c' },
    { kind: 'TokenKind::Eof', text: 'EOF' },
  ];
  return (
    <svg
      viewBox={DIAGRAM_VIEWBOX}
      className="stage-diagram"
      role="img"
      aria-label="Early syntax error for an unparenthesised nullish coalescing mix"
      preserveAspectRatio="xMidYMid meet"
    >
      <SceneHeader title="5 · EARLY ERROR" source="a ?? b || c" />
      <TokenRow tokens={tokens} t={props.t} failing={failing} />
      <g opacity={reveal(props.t, 6, 7)}>
        <Box x={150} y={196} w={420} h={48} stroke={BOARD.fail} progress={reveal(props.t, 6, 7)} />
        <Label x={168} y={216} color={BOARD.fail} size={10} weight={600}>
          {'SYNTAXDIAGNOSTIC { KIND: DIAGNOSTICKIND::UNPARENTHESIZEDNULLISHANDLOGICALMIX }'}
        </Label>
        <Label x={168} y={234} color={BOARD.fail} size={9}>
          ?? MIXED WITH || WITHOUT PARENTHESES IS A SYNTAX ERROR, NOT A PRECEDENCE RULE.
        </Label>
      </g>
      <Label x={150} y={268} color={BOARD.rib} size={9}>
        THE CHECK RUNS WHILE THE ?? NODE IS EMITTED, AGAINST BOTH OPERANDS.
      </Label>
    </svg>
  );
}

/**
 * The steps of the scene, in pipeline order: token stream → binding powers →
 * precedence climbing → AST → the early-error guard.
 *
 * Exported so the clause of every step can be asserted on directly — the
 * requirement is that each step names a real clause or invariant, and that
 * is only checkable if the whole table is reachable.
 */
export const PRATT_PARSER_STEPS: Step[] = [
  {
    caption:
      'The lexer turns the source into an executable token stream; the parser never reads the source again.',
    clause: 'ECMA-262 §12 (Lexical Grammar) — vjs_syntax tokenize (J3); punctuators §12.8.1',
    render: (t) => <TokenStreamStep t={t} />,
  },
  {
    caption:
      'Each binary operator carries a left and a right binding power. L_BP < R_BP makes every binary operator left-associative.',
    clause: 'ECMA-262 §13.13 — vjs_syntax match_binary_op binding-power table (J3)',
    render: (t) => <BindingPowerStep t={t} />,
  },
  {
    caption:
      'The parser climbs: it parses the left operand, matches the operator, then parses the right side at the operator’s right binding power.',
    clause: 'ECMA-262 §13.13 — vjs_syntax parse_binary_expr precedence climbing (J3)',
    render: (t) => <PrecedenceClimbStep t={t} />,
  },
  {
    caption:
      'The climb emits a binary node. && binds tighter than ||, so the logical-and becomes the right operand of the logical-or.',
    clause: 'ECMA-262 §13.13 — vjs_syntax ExprKind::Binary and Program::grammar_wf (J3)',
    render: (t) => <AstStep t={t} />,
  },
  {
    caption:
      'The same section forbids mixing ?? with && or || without parentheses, and the parser rejects it while building the node.',
    clause:
      'ECMA-262 §13.13 — vjs_syntax DiagnosticKind::UnparenthesizedNullishAndLogicalMix (J3)',
  render: (t) => <EarlyErrorStep t={t} />,
  },
];

export interface PrattParserSceneProps {
  className?: string;
  /** Accessible name for the scene. */
  title?: string;
}

/**
 * Tier 3 — the Pratt parser step-through scene.
 *
 * A 2D SVG diagram in the manim-dsa tradition, drawn in the drafter grammar.
 * Not WebGL: this is an algorithm trace, not a physical scene.
 */
export function PrattParserScene(props: PrattParserSceneProps = {}): ReactElement {
  const { className, title = 'Pratt parser step-through' } = props;
  const steps = PRATT_PARSER_STEPS;
  return (
    <section
      className={className === undefined ? 'stage-scene' : `stage-scene ${className}`}
      data-testid="pratt-parser-scene"
      aria-label={title}
    >
      <Stepper steps={steps} label={title} />
    </section>
  );
}

/** The scene title block, exported so the gallery can reuse the register. */
export const PRATT_SCENE_TITLE = MONO_TITLE;
