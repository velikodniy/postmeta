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
    /// String-specific unary: `str`, `char`, `decimal`, `readfrom`.
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
    // Type tests and conversions
    Not = 38,
    Sqrt = 39,
    MExp = 40,
    MLog = 41,
    SinD = 42,
    CosD = 43,
    Floor = 44,
    UniformDeviate = 45,
    CharExists = 46,
    FontSize = 47,
    // Part extractors
    LLCorner = 48,
    LRCorner = 49,
    ULCorner = 50,
    URCorner = 51,
    ArcLength = 52,
    Angle = 53,
    CycleOp = 54,
    FilledOp = 55,
    StrokedOp = 56,
    TextualOp = 57,
    ClippedOp = 58,
    BoundedOp = 59,
    MakePath = 60,
    MakePen = 61,
    Oct = 62,
    Hex = 63,
    ASCII = 64,
    Char = 65,
    Length = 66,
    TurningNumber = 67,
    XPart = 68,
    YPart = 69,
    XXPart = 70,
    XYPart = 71,
    YXPart = 72,
    YYPart = 73,
    RedPart = 74,
    GreenPart = 75,
    BluePart = 76,
    FontPart = 77,
    TextPart = 78,
    PathPart = 79,
    PenPart = 80,
    DashPart = 81,
    Decimal = 82,
    Reverse = 83,
}

/// Operation codes for [`Command::PrimaryBinary`] ("expr X of Y").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum PrimaryBinaryOp {
    PointOf = 84,
    PrecontrolOf = 85,
    PostcontrolOf = 86,
    PenOffsetOf = 87,
    DirectionOf = 88,
    SubpathOf = 89,
    DirectionTimeOf = 90,
    ArcTimeOf = 91,
    SubstringOf = 115,
}

/// Operation codes for [`Command::SecondaryBinary`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum SecondaryBinaryOp {
    Times = 92,
    Over = 93,
    Scaled = 94,
    Shifted = 95,
    Rotated = 96,
    XScaled = 97,
    YScaled = 98,
    Slanted = 99,
    ZScaled = 100,
    Transformed = 101,
    DotProd = 102,
    Infont = 112,
}

/// Operation codes for [`Command::TertiaryBinary`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum TertiaryBinaryOp {
    PythagAdd = 103,
    PythagSub = 104,
    Or = 105,
}

/// Operation codes for [`Command::ExpressionBinary`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum ExpressionBinaryOp {
    LessThan = 106,
    LessOrEqual = 107,
    GreaterThan = 108,
    GreaterOrEqual = 109,
    EqualTo = 110,
    UnequalTo = 111,
    Concatenate = 112,
    IntersectionTimes = 113,
}

/// Operation codes for [`Command::PlusOrMinus`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u16)]
pub enum PlusMinusOp {
    Plus = 115,
    Minus = 116,
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
    Char = 1,
    Decimal = 2,
    ReadFrom = 3,
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
    Known = 9,
    Unknown = 10,
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
    Not,
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
    Decimal,
    Reverse,
});
impl_from_modifier!(PrimaryBinaryOp {
    PointOf,
    PrecontrolOf,
    PostcontrolOf,
    PenOffsetOf,
    DirectionOf,
    SubpathOf,
    DirectionTimeOf,
    ArcTimeOf,
    SubstringOf,
});
impl_from_modifier!(SecondaryBinaryOp {
    Times,
    Over,
    Scaled,
    Shifted,
    Rotated,
    XScaled,
    YScaled,
    Slanted,
    ZScaled,
    Transformed,
    DotProd,
    Infont,
});
impl_from_modifier!(TertiaryBinaryOp {
    PythagAdd,
    PythagSub,
    Or,
});
impl_from_modifier!(ExpressionBinaryOp {
    LessThan,
    LessOrEqual,
    GreaterThan,
    GreaterOrEqual,
    EqualTo,
    UnequalTo,
    Concatenate,
    IntersectionTimes,
});
impl_from_modifier!(PlusMinusOp { Plus, Minus });
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
impl_from_modifier!(StrOpOp {
    Str,
    Char,
    Decimal,
    ReadFrom,
});
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
    Known,
    Unknown,
});

// ---------------------------------------------------------------------------
// Primitive table
// ---------------------------------------------------------------------------

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
        command: Command::TypeName,
        modifier: TypeNameOp::Known as u16,
    },
    Primitive {
        name: "unknown",
        command: Command::TypeName,
        modifier: TypeNameOp::Unknown as u16,
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
        name: "uniformdeviate",
        command: Command::Unary,
        modifier: UnaryOp::UniformDeviate as u16,
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
        command: Command::StrOp,
        modifier: StrOpOp::ReadFrom as u16,
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
        name: "direction",
        command: Command::PrimaryBinary,
        modifier: PrimaryBinaryOp::DirectionOf as u16,
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
        name: "dotprod",
        command: Command::SecondaryBinary,
        modifier: SecondaryBinaryOp::DotProd as u16,
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
    // -- Expression binary --
    Primitive {
        name: "intersectiontimes",
        command: Command::ExpressionBinary,
        modifier: ExpressionBinaryOp::IntersectionTimes as u16,
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
