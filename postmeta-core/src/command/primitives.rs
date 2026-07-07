//! The table of engine primitives: name → (command, modifier) registrations.

use super::{
    BoundsOp, Command, FiOrElseOp, IfTestOp, IterationOp, MacroDefOp, MacroSpecialOp, MessageOp,
    NullaryOp, ParamTypeOp, PrimaryBinaryOp, SecondaryBinaryOp, ShowOp, StrOpOp, TertiaryBinaryOp,
    ThingToAddOp, TypeNameOp, UnaryOp, WithOptionOp,
};

/// A primitive registration entry: name → (command, modifier).
#[derive(Debug, Clone, Copy)]
pub struct Primitive {
    /// The symbolic name of the primitive.
    pub name: &'static str,
    /// The command code.
    pub command: Command,
    /// The modifier (operation code).
    pub modifier: u16,
}

/// All engine primitives. Registered into the symbol table at startup.
///
/// This list corresponds to `mp.web`'s calls to the `primitive` procedure.
/// User-visible macros like `draw`, `fill`, `fullcircle` etc. are NOT here —
/// they are defined in `plain.mp`.
pub const PRIMITIVES: &[Primitive] = &[
    // -- Expandable commands --
    Primitive {
        name: "if",
        command: Command::IfTest,
        modifier: IfTestOp::If as u16,
    },
    Primitive {
        name: "elseif",
        command: Command::FiOrElse,
        modifier: FiOrElseOp::ElseIf as u16,
    },
    Primitive {
        name: "else",
        command: Command::FiOrElse,
        modifier: FiOrElseOp::Else as u16,
    },
    Primitive {
        name: "fi",
        command: Command::FiOrElse,
        modifier: FiOrElseOp::Fi as u16,
    },
    Primitive {
        name: "input",
        command: Command::Input,
        modifier: 0,
    },
    Primitive {
        name: "for",
        command: Command::Iteration,
        modifier: IterationOp::For as u16,
    },
    Primitive {
        name: "forsuffixes",
        command: Command::Iteration,
        modifier: IterationOp::ForSuffixes as u16,
    },
    Primitive {
        name: "forever",
        command: Command::Iteration,
        modifier: IterationOp::Forever as u16,
    },
    Primitive {
        name: "exitif",
        command: Command::ExitTest,
        modifier: 0,
    },
    Primitive {
        name: "relax",
        command: Command::Relax,
        modifier: 0,
    },
    Primitive {
        name: "scantokens",
        command: Command::ScanTokens,
        modifier: 0,
    },
    Primitive {
        name: "expandafter",
        command: Command::ExpandAfter,
        modifier: 0,
    },
    Primitive {
        name: "btex",
        command: Command::StartTex,
        modifier: 0,
    },
    Primitive {
        name: "etex",
        command: Command::EtexMarker,
        modifier: 0,
    },
    Primitive {
        name: "verbatimtex",
        command: Command::VerbatimTex,
        modifier: 0,
    },
    // -- Statement-level commands --
    Primitive {
        name: "outer",
        command: Command::Outer,
        modifier: 0,
    },
    Primitive {
        name: "save",
        command: Command::Save,
        modifier: 0,
    },
    Primitive {
        name: "interim",
        command: Command::Interim,
        modifier: 0,
    },
    Primitive {
        name: "let",
        command: Command::Let,
        modifier: 0,
    },
    Primitive {
        name: "newinternal",
        command: Command::NewInternal,
        modifier: 0,
    },
    Primitive {
        name: "def",
        command: Command::MacroDef,
        modifier: MacroDefOp::Def as u16,
    },
    Primitive {
        name: "vardef",
        command: Command::MacroDef,
        modifier: MacroDefOp::VarDef as u16,
    },
    Primitive {
        name: "primarydef",
        command: Command::MacroDef,
        modifier: MacroDefOp::PrimaryDef as u16,
    },
    Primitive {
        name: "secondarydef",
        command: Command::MacroDef,
        modifier: MacroDefOp::SecondaryDef as u16,
    },
    Primitive {
        name: "tertiarydef",
        command: Command::MacroDef,
        modifier: MacroDefOp::TertiaryDef as u16,
    },
    Primitive {
        name: "enddef",
        command: Command::MacroSpecial,
        modifier: MacroSpecialOp::EndDef as u16,
    },
    Primitive {
        name: "endfor",
        command: Command::MacroSpecial,
        modifier: MacroSpecialOp::EndFor as u16,
    },
    // Suffix parameter markers for vardef (mp.web §12615)
    Primitive {
        name: "#@",
        command: Command::MacroSpecial,
        modifier: MacroSpecialOp::MacroPrefix as u16,
    },
    Primitive {
        name: "@",
        command: Command::MacroSpecial,
        modifier: MacroSpecialOp::MacroAt as u16,
    },
    Primitive {
        name: "@#",
        command: Command::MacroSpecial,
        modifier: MacroSpecialOp::MacroSuffix as u16,
    },
    Primitive {
        name: "shipout",
        command: Command::ShipOut,
        modifier: 0,
    },
    Primitive {
        name: "addto",
        command: Command::AddTo,
        modifier: 0,
    },
    Primitive {
        name: "clip",
        command: Command::Bounds,
        modifier: BoundsOp::Clip as u16,
    },
    Primitive {
        name: "setbounds",
        command: Command::Bounds,
        modifier: BoundsOp::SetBounds as u16,
    },
    Primitive {
        name: "show",
        command: Command::Show,
        modifier: ShowOp::Show as u16,
    },
    Primitive {
        name: "showtoken",
        command: Command::Show,
        modifier: ShowOp::ShowToken as u16,
    },
    Primitive {
        name: "showdependencies",
        command: Command::Show,
        modifier: ShowOp::ShowDependencies as u16,
    },
    Primitive {
        name: "showvariable",
        command: Command::Show,
        modifier: ShowOp::ShowVariable as u16,
    },
    Primitive {
        name: "showstats",
        command: Command::Show,
        modifier: ShowOp::ShowStats as u16,
    },
    Primitive {
        name: "batchmode",
        command: Command::ModeCommand,
        modifier: 0,
    },
    Primitive {
        name: "nonstopmode",
        command: Command::ModeCommand,
        modifier: 1,
    },
    Primitive {
        name: "scrollmode",
        command: Command::ModeCommand,
        modifier: 2,
    },
    Primitive {
        name: "errorstopmode",
        command: Command::ModeCommand,
        modifier: 3,
    },
    Primitive {
        name: "randomseed",
        command: Command::RandomSeed,
        modifier: 0,
    },
    Primitive {
        name: "message",
        command: Command::MessageCommand,
        modifier: MessageOp::Message as u16,
    },
    Primitive {
        name: "errmessage",
        command: Command::MessageCommand,
        modifier: MessageOp::ErrMessage as u16,
    },
    Primitive {
        name: "errhelp",
        command: Command::MessageCommand,
        modifier: MessageOp::ErrHelp as u16,
    },
    Primitive {
        name: "everyjob",
        command: Command::EveryJob,
        modifier: 0,
    },
    Primitive {
        name: "delimiters",
        command: Command::Delimiters,
        modifier: 0,
    },
    Primitive {
        name: "special",
        command: Command::Special,
        modifier: 0,
    },
    Primitive {
        name: "write",
        command: Command::Write,
        modifier: 0,
    },
    // -- Type names --
    Primitive {
        name: "boolean",
        command: Command::TypeName,
        modifier: TypeNameOp::Boolean as u16,
    },
    Primitive {
        name: "string",
        command: Command::TypeName,
        modifier: TypeNameOp::String as u16,
    },
    Primitive {
        name: "pen",
        command: Command::TypeName,
        modifier: TypeNameOp::Pen as u16,
    },
    Primitive {
        name: "path",
        command: Command::TypeName,
        modifier: TypeNameOp::Path as u16,
    },
    Primitive {
        name: "picture",
        command: Command::TypeName,
        modifier: TypeNameOp::Picture as u16,
    },
    Primitive {
        name: "transform",
        command: Command::TypeName,
        modifier: TypeNameOp::Transform as u16,
    },
    Primitive {
        name: "color",
        command: Command::TypeName,
        modifier: TypeNameOp::Color as u16,
    },
    Primitive {
        name: "pair",
        command: Command::TypeName,
        modifier: TypeNameOp::Pair as u16,
    },
    Primitive {
        name: "numeric",
        command: Command::TypeName,
        modifier: TypeNameOp::Numeric as u16,
    },
    Primitive {
        name: "known",
        command: Command::Unary,
        modifier: UnaryOp::KnownOp as u16,
    },
    Primitive {
        name: "unknown",
        command: Command::Unary,
        modifier: UnaryOp::UnknownOp as u16,
    },
    // -- Delimiters & grouping --
    Primitive {
        name: "begingroup",
        command: Command::BeginGroup,
        modifier: 0,
    },
    Primitive {
        name: "endgroup",
        command: Command::EndGroup,
        modifier: 0,
    },
    // -- Nullary operators --
    Primitive {
        name: "true",
        command: Command::Nullary,
        modifier: NullaryOp::True as u16,
    },
    Primitive {
        name: "false",
        command: Command::Nullary,
        modifier: NullaryOp::False as u16,
    },
    Primitive {
        name: "nullpicture",
        command: Command::Nullary,
        modifier: NullaryOp::NullPicture as u16,
    },
    Primitive {
        name: "nullpen",
        command: Command::Nullary,
        modifier: NullaryOp::NullPen as u16,
    },
    Primitive {
        name: "jobname",
        command: Command::Nullary,
        modifier: NullaryOp::JobName as u16,
    },
    Primitive {
        name: "readstring",
        command: Command::Nullary,
        modifier: NullaryOp::ReadString as u16,
    },
    Primitive {
        name: "pencircle",
        command: Command::Nullary,
        modifier: NullaryOp::PenCircle as u16,
    },
    Primitive {
        name: "normaldeviate",
        command: Command::Nullary,
        modifier: NullaryOp::NormalDeviate as u16,
    },
    // -- Unary operators --
    Primitive {
        name: "not",
        command: Command::Unary,
        modifier: UnaryOp::Not as u16,
    },
    Primitive {
        name: "sqrt",
        command: Command::Unary,
        modifier: UnaryOp::Sqrt as u16,
    },
    Primitive {
        name: "mexp",
        command: Command::Unary,
        modifier: UnaryOp::MExp as u16,
    },
    Primitive {
        name: "mlog",
        command: Command::Unary,
        modifier: UnaryOp::MLog as u16,
    },
    Primitive {
        name: "sind",
        command: Command::Unary,
        modifier: UnaryOp::SinD as u16,
    },
    Primitive {
        name: "cosd",
        command: Command::Unary,
        modifier: UnaryOp::CosD as u16,
    },
    Primitive {
        name: "floor",
        command: Command::Unary,
        modifier: UnaryOp::Floor as u16,
    },
    Primitive {
        name: "odd",
        command: Command::Unary,
        modifier: UnaryOp::Odd as u16,
    },
    Primitive {
        name: "uniformdeviate",
        command: Command::Unary,
        modifier: UnaryOp::UniformDeviate as u16,
    },
    Primitive {
        name: "charexists",
        command: Command::Unary,
        modifier: UnaryOp::CharExists as u16,
    },
    Primitive {
        name: "fontsize",
        command: Command::Unary,
        modifier: UnaryOp::FontSize as u16,
    },
    Primitive {
        name: "angle",
        command: Command::Unary,
        modifier: UnaryOp::Angle as u16,
    },
    Primitive {
        name: "cycle",
        command: Command::Cycle,
        modifier: 0,
    },
    Primitive {
        name: "makepath",
        command: Command::Unary,
        modifier: UnaryOp::MakePath as u16,
    },
    Primitive {
        name: "makepen",
        command: Command::Unary,
        modifier: UnaryOp::MakePen as u16,
    },
    Primitive {
        name: "oct",
        command: Command::Unary,
        modifier: UnaryOp::Oct as u16,
    },
    Primitive {
        name: "hex",
        command: Command::Unary,
        modifier: UnaryOp::Hex as u16,
    },
    Primitive {
        name: "ASCII",
        command: Command::Unary,
        modifier: UnaryOp::ASCII as u16,
    },
    Primitive {
        name: "char",
        command: Command::Unary,
        modifier: UnaryOp::Char as u16,
    },
    Primitive {
        name: "length",
        command: Command::Unary,
        modifier: UnaryOp::Length as u16,
    },
    Primitive {
        name: "turningnumber",
        command: Command::Unary,
        modifier: UnaryOp::TurningNumber as u16,
    },
    Primitive {
        name: "xpart",
        command: Command::Unary,
        modifier: UnaryOp::XPart as u16,
    },
    Primitive {
        name: "ypart",
        command: Command::Unary,
        modifier: UnaryOp::YPart as u16,
    },
    Primitive {
        name: "xxpart",
        command: Command::Unary,
        modifier: UnaryOp::XXPart as u16,
    },
    Primitive {
        name: "xypart",
        command: Command::Unary,
        modifier: UnaryOp::XYPart as u16,
    },
    Primitive {
        name: "yxpart",
        command: Command::Unary,
        modifier: UnaryOp::YXPart as u16,
    },
    Primitive {
        name: "yypart",
        command: Command::Unary,
        modifier: UnaryOp::YYPart as u16,
    },
    Primitive {
        name: "redpart",
        command: Command::Unary,
        modifier: UnaryOp::RedPart as u16,
    },
    Primitive {
        name: "greenpart",
        command: Command::Unary,
        modifier: UnaryOp::GreenPart as u16,
    },
    Primitive {
        name: "bluepart",
        command: Command::Unary,
        modifier: UnaryOp::BluePart as u16,
    },
    Primitive {
        name: "colormodel",
        command: Command::Unary,
        modifier: UnaryOp::ColorModel as u16,
    },
    Primitive {
        name: "greypart",
        command: Command::Unary,
        modifier: UnaryOp::GreyPart as u16,
    },
    Primitive {
        name: "cyanpart",
        command: Command::Unary,
        modifier: UnaryOp::CyanPart as u16,
    },
    Primitive {
        name: "magentapart",
        command: Command::Unary,
        modifier: UnaryOp::MagentaPart as u16,
    },
    Primitive {
        name: "yellowpart",
        command: Command::Unary,
        modifier: UnaryOp::YellowPart as u16,
    },
    Primitive {
        name: "blackpart",
        command: Command::Unary,
        modifier: UnaryOp::BlackPart as u16,
    },
    Primitive {
        name: "fontpart",
        command: Command::Unary,
        modifier: UnaryOp::FontPart as u16,
    },
    Primitive {
        name: "textpart",
        command: Command::Unary,
        modifier: UnaryOp::TextPart as u16,
    },
    Primitive {
        name: "pathpart",
        command: Command::Unary,
        modifier: UnaryOp::PathPart as u16,
    },
    Primitive {
        name: "penpart",
        command: Command::Unary,
        modifier: UnaryOp::PenPart as u16,
    },
    Primitive {
        name: "dashpart",
        command: Command::Unary,
        modifier: UnaryOp::DashPart as u16,
    },
    Primitive {
        name: "decimal",
        command: Command::Unary,
        modifier: UnaryOp::Decimal as u16,
    },
    Primitive {
        name: "reverse",
        command: Command::Unary,
        modifier: UnaryOp::Reverse as u16,
    },
    Primitive {
        name: "llcorner",
        command: Command::Unary,
        modifier: UnaryOp::LLCorner as u16,
    },
    Primitive {
        name: "lrcorner",
        command: Command::Unary,
        modifier: UnaryOp::LRCorner as u16,
    },
    Primitive {
        name: "ulcorner",
        command: Command::Unary,
        modifier: UnaryOp::ULCorner as u16,
    },
    Primitive {
        name: "urcorner",
        command: Command::Unary,
        modifier: UnaryOp::URCorner as u16,
    },
    Primitive {
        name: "arclength",
        command: Command::Unary,
        modifier: UnaryOp::ArcLength as u16,
    },
    Primitive {
        name: "filled",
        command: Command::Unary,
        modifier: UnaryOp::FilledOp as u16,
    },
    Primitive {
        name: "stroked",
        command: Command::Unary,
        modifier: UnaryOp::StrokedOp as u16,
    },
    Primitive {
        name: "textual",
        command: Command::Unary,
        modifier: UnaryOp::TextualOp as u16,
    },
    Primitive {
        name: "clipped",
        command: Command::Unary,
        modifier: UnaryOp::ClippedOp as u16,
    },
    Primitive {
        name: "bounded",
        command: Command::Unary,
        modifier: UnaryOp::BoundedOp as u16,
    },
    // -- String operators --
    Primitive {
        name: "str",
        command: Command::StrOp,
        modifier: StrOpOp::Str as u16,
    },
    Primitive {
        name: "readfrom",
        command: Command::Unary,
        modifier: UnaryOp::ReadFrom as u16,
    },
    // -- Primary binary ("X of Y") --
    Primitive {
        name: "point",
        command: Command::PrimaryBinary,
        modifier: PrimaryBinaryOp::PointOf as u16,
    },
    Primitive {
        name: "precontrol",
        command: Command::PrimaryBinary,
        modifier: PrimaryBinaryOp::PrecontrolOf as u16,
    },
    Primitive {
        name: "postcontrol",
        command: Command::PrimaryBinary,
        modifier: PrimaryBinaryOp::PostcontrolOf as u16,
    },
    Primitive {
        name: "penoffset",
        command: Command::PrimaryBinary,
        modifier: PrimaryBinaryOp::PenOffsetOf as u16,
    },
    Primitive {
        name: "subpath",
        command: Command::PrimaryBinary,
        modifier: PrimaryBinaryOp::SubpathOf as u16,
    },
    Primitive {
        name: "directiontime",
        command: Command::PrimaryBinary,
        modifier: PrimaryBinaryOp::DirectionTimeOf as u16,
    },
    Primitive {
        name: "arctime",
        command: Command::PrimaryBinary,
        modifier: PrimaryBinaryOp::ArcTimeOf as u16,
    },
    // -- Secondary binary --
    Primitive {
        name: "scaled",
        command: Command::SecondaryBinary,
        modifier: SecondaryBinaryOp::Scaled as u16,
    },
    Primitive {
        name: "shifted",
        command: Command::SecondaryBinary,
        modifier: SecondaryBinaryOp::Shifted as u16,
    },
    Primitive {
        name: "rotated",
        command: Command::SecondaryBinary,
        modifier: SecondaryBinaryOp::Rotated as u16,
    },
    Primitive {
        name: "xscaled",
        command: Command::SecondaryBinary,
        modifier: SecondaryBinaryOp::XScaled as u16,
    },
    Primitive {
        name: "yscaled",
        command: Command::SecondaryBinary,
        modifier: SecondaryBinaryOp::YScaled as u16,
    },
    Primitive {
        name: "slanted",
        command: Command::SecondaryBinary,
        modifier: SecondaryBinaryOp::Slanted as u16,
    },
    Primitive {
        name: "zscaled",
        command: Command::SecondaryBinary,
        modifier: SecondaryBinaryOp::ZScaled as u16,
    },
    Primitive {
        name: "transformed",
        command: Command::SecondaryBinary,
        modifier: SecondaryBinaryOp::Transformed as u16,
    },
    Primitive {
        name: "infont",
        command: Command::SecondaryBinary,
        modifier: SecondaryBinaryOp::Infont as u16,
    },
    Primitive {
        name: "and",
        command: Command::And,
        modifier: 0,
    },
    // -- Tertiary binary --
    Primitive {
        name: "or",
        command: Command::TertiaryBinary,
        modifier: TertiaryBinaryOp::Or as u16,
    },
    // -- Tertiary binary (continued) --
    Primitive {
        name: "intersectiontimes",
        command: Command::TertiaryBinary,
        modifier: TertiaryBinaryOp::IntersectionTimes as u16,
    },
    Primitive {
        name: "substring",
        command: Command::PrimaryBinary,
        modifier: PrimaryBinaryOp::SubstringOf as u16,
    },
    // -- Comparison (use ExpressionBinary) --
    // In MetaPost, < > = are handled specially. The scanner produces symbolic
    // tokens; the symbol table maps them to the right commands.

    // -- Path construction --
    Primitive {
        name: "controls",
        command: Command::Controls,
        modifier: 0,
    },
    Primitive {
        name: "tension",
        command: Command::Tension,
        modifier: 0,
    },
    Primitive {
        name: "atleast",
        command: Command::AtLeast,
        modifier: 0,
    },
    Primitive {
        name: "curl",
        command: Command::CurlCommand,
        modifier: 0,
    },
    // -- Drawing options --
    Primitive {
        name: "withpen",
        command: Command::WithOption,
        modifier: WithOptionOp::WithPen as u16,
    },
    Primitive {
        name: "withcolor",
        command: Command::WithOption,
        modifier: WithOptionOp::WithColor as u16,
    },
    Primitive {
        name: "dashed",
        command: Command::WithOption,
        modifier: WithOptionOp::Dashed as u16,
    },
    Primitive {
        name: "contour",
        command: Command::ThingToAdd,
        modifier: ThingToAddOp::Contour as u16,
    },
    Primitive {
        name: "doublepath",
        command: Command::ThingToAdd,
        modifier: ThingToAddOp::DoublePath as u16,
    },
    Primitive {
        name: "also",
        command: Command::ThingToAdd,
        modifier: ThingToAddOp::Also as u16,
    },
    // -- Keywords --
    Primitive {
        name: "of",
        command: Command::OfToken,
        modifier: 0,
    },
    Primitive {
        name: "to",
        command: Command::ToToken,
        modifier: 0,
    },
    Primitive {
        name: "step",
        command: Command::StepToken,
        modifier: 0,
    },
    Primitive {
        name: "until",
        command: Command::UntilToken,
        modifier: 0,
    },
    Primitive {
        name: "within",
        command: Command::WithinToken,
        modifier: 0,
    },
    // -- Macro parameter type markers --
    Primitive {
        name: "expr",
        command: Command::ParamType,
        modifier: ParamTypeOp::Expr as u16,
    },
    Primitive {
        name: "suffix",
        command: Command::ParamType,
        modifier: ParamTypeOp::Suffix as u16,
    },
    Primitive {
        name: "text",
        command: Command::ParamType,
        modifier: ParamTypeOp::Text as u16,
    },
    Primitive {
        name: "primary",
        command: Command::ParamType,
        modifier: ParamTypeOp::Primary as u16,
    },
    Primitive {
        name: "secondary",
        command: Command::ParamType,
        modifier: ParamTypeOp::Secondary as u16,
    },
    Primitive {
        name: "tertiary",
        command: Command::ParamType,
        modifier: ParamTypeOp::Tertiary as u16,
    },
    // -- End / dump --
    Primitive {
        name: "end",
        command: Command::Stop,
        modifier: 0,
    },
    Primitive {
        name: "dump",
        command: Command::Stop,
        modifier: 1,
    },
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn primitives_have_unique_names() {
        use std::collections::HashSet;
        let mut names = HashSet::new();
        for p in PRIMITIVES {
            assert!(
                names.insert(p.name),
                "duplicate primitive name: {:?}",
                p.name
            );
        }
    }

    #[test]
    fn primitive_count() {
        // We should have a substantial number of primitives
        assert!(
            PRIMITIVES.len() >= 130,
            "too few primitives: {}",
            PRIMITIVES.len()
        );
    }
}
