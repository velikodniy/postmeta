//! Command codes and operation codes for `MetaPost` primitives.
//!
//! Every symbolic token maps to a `(Command, u16)` pair where:
//! - `Command` determines the syntactic role (can it start an expression?
//!   is it a statement keyword? is it an operator at some precedence level?)
//! - The `u16` modifier further identifies the specific primitive within
//!   that command category.
//!
//! The command code ordering mirrors `mp.web` §12 and is critical for
//! the expression parser's precedence logic.

// ---------------------------------------------------------------------------
// Command codes
// ---------------------------------------------------------------------------

/// Syntactic command categories.
///
/// The numeric values matter: the expression parser uses range checks
/// (e.g. `min_primary_command..=max_primary_command`) to decide what can
/// appear at each precedence level.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u8)]
pub enum Command {
    // -- Expandable commands (eliminated during macro expansion) --
    /// `btex ... etex` start marker.
    StartTex = 1,
    /// `etex` marker.
    EtexMarker = 2,
    /// `verbatimtex ... etex` — skip TeX preamble material.
    VerbatimTex = 3,
    /// `if` / `elseif` test.
    IfTest = 4,
    /// `fi` / `else` / `elseif`.
    FiOrElse = 5,
    /// `input`.
    Input = 6,
    /// `for` / `forsuffixes` / `forever`.
    Iteration = 7,
    /// Internal repeat-loop token.
    RepeatLoop = 8,
    /// `exitif`.
    ExitTest = 9,
    /// `relax`.
    Relax = 10,
    /// `scantokens`.
    ScanTokens = 11,
    /// `expandafter`.
    ExpandAfter = 12,
    /// A defined macro being expanded.
    DefinedMacro = 13,

    // -- Statement-level commands (min_command = 14) --
    /// `save`.
    Save = 14,
    /// `interim`.
    Interim = 15,
    /// `let`.
    Let = 16,
    /// `newinternal`.
    NewInternal = 17,
    /// `def` / `vardef` / `primarydef` / `secondarydef` / `tertiarydef`.
    MacroDef = 18,
    /// `shipout`.
    ShipOut = 19,
    /// `addto`.
    AddTo = 20,
    /// `clip` / `setbounds` (`bounds_command` in `mp.web`).
    Bounds = 21,
    /// `outer` — marks tokens as outer (not yet enforced, but parsed).
    Outer = 22,
    /// `show` / `showtoken` / `showdependencies` / `showvariable` / `showstats`.
    Show = 24,
    /// `batchmode` / `nonstopmode` / `scrollmode` / `errorstopmode`.
    ModeCommand = 25,
    /// `randomseed`.
    RandomSeed = 26,
    /// `message` / `errmessage` / `errhelp`.
    MessageCommand = 27,
    /// `everyjob`.
    EveryJob = 28,
    /// `delimiters`.
    Delimiters = 29,
    /// `special`.
    Special = 30,
    /// `write`.
    Write = 31,

    // -- Primary commands (can start expressions) --
    /// Type names: `numeric`, `pair`, `path`, `pen`, `picture`, `color`,
    /// `transform`, `string`, `boolean`.
    TypeName = 32,
    /// A left delimiter (e.g. `(` or user-defined).
    LeftDelimiter = 33,
    /// `begingroup`.
    BeginGroup = 34,
    /// Nullary operators: `true`, `false`, `nullpicture`, `nullpen`,
    /// `pencircle`, `normaldeviate`, `readstring`, `jobname`.
    Nullary = 35,
    /// Unary operators: `not`, `sqrt`, `sind`, `cosd`, `floor`, `length`,
    /// `abs`, `xpart`, `ypart`, `xxpart`, etc.
    Unary = 36,
    /// String-specific unary: `str`.
    StrOp = 37,
    /// `cycle`.
    Cycle = 38,
    /// `of`-binary operators: `point ... of`, `subpath ... of`,
    /// `direction ... of`, `penoffset ... of`, etc.
    PrimaryBinary = 39,
    /// Internal capsule (intermediate expression result).
    CapsuleToken = 40,
    /// A string literal token.
    StringToken = 41,
    /// Internal quantities: `linecap`, `linejoin`, `tracingchoices`, etc.
    InternalQuantity = 42,
    /// An unresolved variable name (tag).
    TagToken = 43,
    /// A numeric literal token.
    NumericToken = 44,

    // -- Tertiary-level operators --
    /// `+` / `-` (also unary minus).
    PlusOrMinus = 45,
    /// A user-defined `tertiarydef` macro.
    TertiarySecondaryMacro = 46,
    /// Built-in tertiary binary: `++`, `+-+`.
    TertiaryBinary = 47,

    // -- Expression-level operators --
    /// `{` (left brace, for path directions).
    LeftBrace = 48,
    /// `..` (path join).
    PathJoin = 49,
    /// `&` (concatenation / path join).
    Ampersand = 50,
    /// A user-defined `secondarydef` macro at expression level.
    ExpressionTertiaryMacro = 51,
    /// Built-in expression binary: `intersectiontimes`.
    ExpressionBinary = 52,
    /// `=` (equation).
    Equals = 53,

    // -- Secondary-level operators --
    /// `and`.
    And = 54,
    /// A user-defined `primarydef` macro.
    SecondaryPrimaryMacro = 55,
    /// `/` (slash — always secondary).
    Slash = 56,
    /// Built-in secondary binary: `*`, `scaled`, `shifted`, `rotated`,
    /// `xscaled`, `yscaled`, `slanted`, `zscaled`, `transformed`,
    /// `dotprod`.
    SecondaryBinary = 57,

    // -- Non-expression tokens --
    /// Parameter type marker in macro definitions.
    ParamType = 58,
    /// `controls` (in path joins).
    Controls = 59,
    /// `tension` (in path joins).
    Tension = 60,
    /// `atleast` (in tension specs).
    AtLeast = 61,
    /// `curl` (in path joins).
    CurlCommand = 62,
    /// Macro-definition specifiers: `#@`, `@`, `@#`, `vardef`, etc.
    MacroSpecial = 63,
    /// A right delimiter (e.g. `)` or user-defined).
    RightDelimiter = 64,
    /// `[` (left bracket — for mediation `a[b,c]`).
    LeftBracket = 65,
    /// `]` (right bracket).
    RightBracket = 66,
    /// `}` (right brace).
    RightBrace = 67,
    /// `withpen` / `withcolor` / `dashed`.
    WithOption = 68,
    /// `contour` / `doublepath` / `also`.
    ThingToAdd = 69,
    /// `of`.
    OfToken = 70,
    /// `to`.
    ToToken = 71,
    /// `step`.
    StepToken = 72,
    /// `until`.
    UntilToken = 73,
    /// `within` (for `for ... within`).
    WithinToken = 74,
    /// `:=` (assignment).
    Assignment = 76,
    /// `::` (double colon in path syntax).
    DoubleColon = 79,
    /// `:` (colon).
    Colon = 80,
    /// `,` (comma).
    Comma = 81,
    /// `;` (semicolon — statement terminator).
    Semicolon = 82,
    /// `endgroup`.
    EndGroup = 83,
    /// `end` / `dump`.
    Stop = 84,
}

impl Command {
    /// Pratt-style binding power for expression-level operators.
    pub const BP_EXPRESSION: u8 = 10;
    /// Pratt-style binding power for tertiary operators.
    pub const BP_TERTIARY: u8 = 20;
    /// Pratt-style binding power for secondary operators.
    pub const BP_SECONDARY: u8 = 30;

    /// Minimum command code that survives macro expansion.
    pub const MIN_COMMAND: Self = Self::Save;

    /// Is this a secondary-level binary operator?
    #[must_use]
    pub const fn is_secondary_op(self) -> bool {
        (self as u8) >= (Self::And as u8) && (self as u8) <= (Self::SecondaryBinary as u8)
    }

    /// Is this a tertiary-level binary operator?
    #[must_use]
    pub const fn is_tertiary_op(self) -> bool {
        (self as u8) >= (Self::PlusOrMinus as u8) && (self as u8) <= (Self::TertiaryBinary as u8)
    }

    /// Is this an expression-level binary operator?
    #[must_use]
    pub const fn is_expression_op(self) -> bool {
        (self as u8) >= (Self::LeftBrace as u8) && (self as u8) <= (Self::Equals as u8)
    }

    /// Return Pratt-style infix binding power for this command.
    #[must_use]
    pub const fn infix_binding_power(self) -> Option<u8> {
        if self.is_secondary_op() {
            Some(Self::BP_SECONDARY)
        } else if self.is_tertiary_op() {
            Some(Self::BP_TERTIARY)
        } else if self.is_expression_op() {
            Some(Self::BP_EXPRESSION)
        } else {
            None
        }
    }

    /// Is this an expandable command (should be expanded before parsing)?
    #[must_use]
    pub const fn is_expandable(self) -> bool {
        (self as u8) < (Self::MIN_COMMAND as u8)
    }

    /// Does this command mark end of statement (`cur_cmd > comma`)?
    #[must_use]
    pub const fn ends_statement(self) -> bool {
        (self as u8) > (Self::Comma as u8)
    }

    /// Can this command trigger implicit multiplication when preceded by
    /// a numeric token?
    ///
    /// In `mp.web` §15381: `cur_cmd >= min_primary_command` (32) and
    /// `cur_cmd < numeric_token` (44).  This covers everything that can
    /// start a primary expression except `+`/`-` and another number.
    #[must_use]
    pub const fn can_start_implicit_mul(self) -> bool {
        let code = self as u8;
        code >= (Self::TypeName as u8) && code < (Self::NumericToken as u8)
    }
}

// ---------------------------------------------------------------------------
// Operation codes (modifiers)
// ---------------------------------------------------------------------------

/// Operation codes for [`Command::Nullary`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum NullaryOp {
    True = 30,
    False = 31,
    NullPicture = 32,
    NullPen = 33,
    JobName = 34,
    ReadString = 35,
    PenCircle = 36,
    NormalDeviate = 37,
}

/// Operation codes for [`Command::Unary`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum UnaryOp {
    Odd = 40,
    Not = 43,
    Decimal = 44,
    Reverse = 45,
    MakePath = 46,
    MakePen = 47,
    Oct = 48,
    Hex = 49,
    ASCII = 50,
    Char = 51,
    Length = 52,
    TurningNumber = 53,
    // Part extractors
    XPart = 54,
    YPart = 55,
    XXPart = 56,
    XYPart = 57,
    YXPart = 58,
    YYPart = 59,
    RedPart = 60,
    GreenPart = 61,
    BluePart = 62,
    FontPart = 63,
    TextPart = 64,
    PathPart = 65,
    PenPart = 66,
    DashPart = 67,
    // Math
    Sqrt = 68,
    MExp = 69,
    MLog = 70,
    SinD = 71,
    CosD = 72,
    Floor = 73,
    UniformDeviate = 74,
    CharExists = 75,
    FontSize = 76,
    // Corner / geometry
    LLCorner = 77,
    LRCorner = 78,
    ULCorner = 79,
    URCorner = 80,
    ArcLength = 81,
    Angle = 82,
    CycleOp = 83,
    // Picture queries
    FilledOp = 84,
    StrokedOp = 85,
    TextualOp = 86,
    ClippedOp = 87,
    BoundedOp = 88,
    // I/O (stub — no filesystem in WASM)
    ReadFrom = 89,
    // Type tests
    KnownOp = 90,
    UnknownOp = 91,
    // Color model inspection
    ColorModel = 92,
    GreyPart = 93,
    CyanPart = 94,
    MagentaPart = 95,
    YellowPart = 96,
    BlackPart = 97,
}

/// Operation codes for [`Command::PlusOrMinus`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum PlusMinusOp {
    Plus = 89,
    Minus = 90,
}

/// Operation codes for [`Command::SecondaryBinary`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum SecondaryBinaryOp {
    Times = 91,
    Over = 92,
    Rotated = 104,
    Slanted = 105,
    Scaled = 106,
    Shifted = 107,
    Transformed = 108,
    XScaled = 109,
    YScaled = 110,
    ZScaled = 111,
    Infont = 112,
}

/// Operation codes for [`Command::TertiaryBinary`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum TertiaryBinaryOp {
    PythagAdd = 93,
    PythagSub = 94,
    Or = 95,
    IntersectionTimes = 113,
}

/// Operation codes for [`Command::ExpressionBinary`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum ExpressionBinaryOp {
    LessThan = 97,
    LessOrEqual = 98,
    GreaterThan = 99,
    GreaterOrEqual = 100,
    EqualTo = 101,
    UnequalTo = 102,
    Concatenate = 103,
}

/// Operation codes for [`Command::PrimaryBinary`] ("expr X of Y").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum PrimaryBinaryOp {
    SubstringOf = 115,
    SubpathOf = 116,
    DirectionTimeOf = 117,
    PointOf = 118,
    PrecontrolOf = 119,
    PostcontrolOf = 120,
    PenOffsetOf = 121,
    ArcTimeOf = 122,
}

/// Operation codes for [`Command::Show`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum ShowOp {
    Show = 0,
    ShowToken = 1,
    ShowDependencies = 2,
    ShowVariable = 3,
    ShowStats = 4,
}

/// Operation codes for [`Command::ThingToAdd`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum ThingToAddOp {
    Contour = 0,
    DoublePath = 1,
    Also = 2,
}

/// Operation codes for [`Command::WithOption`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum WithOptionOp {
    WithPen = 0,
    WithColor = 1,
    Dashed = 2,
}

/// Operation codes for [`Command::Bounds`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum BoundsOp {
    Clip = 0,
    SetBounds = 1,
}

/// Operation codes for [`Command::MacroDef`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum MacroDefOp {
    Def = 0,
    VarDef = 1,
    PrimaryDef = 2,
    SecondaryDef = 3,
    TertiaryDef = 4,
}

/// Operation codes for [`Command::MacroSpecial`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum MacroSpecialOp {
    EndDef = 0,
    EndFor = 1,
    MacroPrefix = 2,
    MacroAt = 3,
    MacroSuffix = 4,
}

/// Operation codes for [`Command::FiOrElse`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum FiOrElseOp {
    Fi = 0,
    Else = 1,
    ElseIf = 2,
}

/// Operation codes for [`Command::Iteration`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum IterationOp {
    For = 0,
    ForSuffixes = 1,
    Forever = 2,
}

/// Operation codes for [`Command::MessageCommand`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum MessageOp {
    Message = 0,
    ErrMessage = 1,
    ErrHelp = 2,
}

/// Operation codes for [`Command::StrOp`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum StrOpOp {
    Str = 0,
}

/// Operation codes for [`Command::ParamType`] — macro parameter type markers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum ParamTypeOp {
    Expr = 0,
    Suffix = 1,
    Text = 2,
    Primary = 3,
    Secondary = 4,
    Tertiary = 5,
}

/// Operation codes for [`Command::IfTest`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum IfTestOp {
    If = 0,
    ElseIf = 1,
}

/// Operation codes for [`Command::TypeName`] — which type is declared.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum TypeNameOp {
    Boolean = 0,
    String = 1,
    Pen = 2,
    Path = 3,
    Picture = 4,
    Transform = 5,
    Color = 6,
    Pair = 7,
    Numeric = 8,
}

macro_rules! impl_from_modifier {
    ($enum_name:ident { $($variant:ident),+ $(,)? }) => {
        impl $enum_name {
            #[must_use]
            pub const fn from_modifier(modifier: u16) -> Option<Self> {
                match modifier {
                    $(x if x == Self::$variant as u16 => Some(Self::$variant),)+
                    _ => None,
                }
            }
        }
    };
}

impl_from_modifier!(NullaryOp {
    True,
    False,
    NullPicture,
    NullPen,
    JobName,
    ReadString,
    PenCircle,
    NormalDeviate,
});
impl_from_modifier!(UnaryOp {
    Odd,
    Not,
    Decimal,
    Reverse,
    MakePath,
    MakePen,
    Oct,
    Hex,
    ASCII,
    Char,
    Length,
    TurningNumber,
    XPart,
    YPart,
    XXPart,
    XYPart,
    YXPart,
    YYPart,
    RedPart,
    GreenPart,
    BluePart,
    FontPart,
    TextPart,
    PathPart,
    PenPart,
    DashPart,
    Sqrt,
    MExp,
    MLog,
    SinD,
    CosD,
    Floor,
    UniformDeviate,
    CharExists,
    FontSize,
    LLCorner,
    LRCorner,
    ULCorner,
    URCorner,
    ArcLength,
    Angle,
    CycleOp,
    FilledOp,
    StrokedOp,
    TextualOp,
    ClippedOp,
    BoundedOp,
    ReadFrom,
    KnownOp,
    UnknownOp,
    ColorModel,
    GreyPart,
    CyanPart,
    MagentaPart,
    YellowPart,
    BlackPart,
});
impl_from_modifier!(PlusMinusOp { Plus, Minus });
impl_from_modifier!(SecondaryBinaryOp {
    Times,
    Over,
    Rotated,
    Slanted,
    Scaled,
    Shifted,
    Transformed,
    XScaled,
    YScaled,
    ZScaled,
    Infont,
});
impl_from_modifier!(TertiaryBinaryOp {
    PythagAdd,
    PythagSub,
    Or,
    IntersectionTimes
});
impl_from_modifier!(ExpressionBinaryOp {
    LessThan,
    LessOrEqual,
    GreaterThan,
    GreaterOrEqual,
    EqualTo,
    UnequalTo,
    Concatenate,
});
impl_from_modifier!(PrimaryBinaryOp {
    SubstringOf,
    SubpathOf,
    DirectionTimeOf,
    PointOf,
    PrecontrolOf,
    PostcontrolOf,
    PenOffsetOf,
    ArcTimeOf,
});
impl_from_modifier!(ShowOp {
    Show,
    ShowToken,
    ShowDependencies,
    ShowVariable,
    ShowStats,
});
impl_from_modifier!(ThingToAddOp {
    Contour,
    DoublePath,
    Also,
});
impl_from_modifier!(WithOptionOp {
    WithPen,
    WithColor,
    Dashed,
});
impl_from_modifier!(BoundsOp { Clip, SetBounds });
impl_from_modifier!(MacroDefOp {
    Def,
    VarDef,
    PrimaryDef,
    SecondaryDef,
    TertiaryDef,
});
impl_from_modifier!(MacroSpecialOp {
    EndDef,
    EndFor,
    MacroPrefix,
    MacroAt,
    MacroSuffix,
});
impl_from_modifier!(FiOrElseOp { Fi, Else, ElseIf });
impl_from_modifier!(IterationOp {
    For,
    ForSuffixes,
    Forever,
});
impl_from_modifier!(MessageOp {
    Message,
    ErrMessage,
    ErrHelp,
});
impl_from_modifier!(StrOpOp { Str });
impl_from_modifier!(ParamTypeOp {
    Expr,
    Suffix,
    Text,
    Primary,
    Secondary,
    Tertiary,
});
impl_from_modifier!(IfTestOp { If, ElseIf });
impl_from_modifier!(TypeNameOp {
    Boolean,
    String,
    Pen,
    Path,
    Picture,
    Transform,
    Color,
    Pair,
    Numeric,
});

// ---------------------------------------------------------------------------
// Primitive table
// ---------------------------------------------------------------------------

mod primitives;

pub use primitives::{PRIMITIVES, Primitive};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn command_ordering_is_correct() {
        // Expandable < min_command
        assert!(Command::IfTest.is_expandable());
        assert!(Command::DefinedMacro.is_expandable());
        assert!(!Command::Save.is_expandable());
    }

    #[test]
    fn secondary_range() {
        assert!(Command::And.is_secondary_op());
        assert!(Command::SecondaryBinary.is_secondary_op());
        assert!(Command::Slash.is_secondary_op());
        assert!(!Command::PlusOrMinus.is_secondary_op());
    }

    #[test]
    fn tertiary_range() {
        assert!(Command::PlusOrMinus.is_tertiary_op());
        assert!(Command::TertiaryBinary.is_tertiary_op());
        assert!(!Command::And.is_tertiary_op());
    }

    #[test]
    fn expression_range() {
        assert!(Command::Equals.is_expression_op());
        assert!(Command::PathJoin.is_expression_op());
        assert!(Command::Ampersand.is_expression_op());
        assert!(!Command::And.is_expression_op());
    }

    #[test]
    fn infix_binding_power_ordering() {
        assert_eq!(
            Command::SecondaryBinary.infix_binding_power(),
            Some(Command::BP_SECONDARY)
        );
        assert_eq!(
            Command::PlusOrMinus.infix_binding_power(),
            Some(Command::BP_TERTIARY)
        );
        assert_eq!(
            Command::Equals.infix_binding_power(),
            Some(Command::BP_EXPRESSION)
        );
        assert_eq!(Command::TagToken.infix_binding_power(), None);
    }

    #[test]
    fn end_of_statement() {
        assert!(Command::Semicolon.ends_statement());
        assert!(Command::EndGroup.ends_statement());
        assert!(Command::Stop.ends_statement());
        assert!(!Command::Comma.ends_statement());
        assert!(!Command::Equals.ends_statement());
    }
}
