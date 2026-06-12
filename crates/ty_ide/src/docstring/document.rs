use indexmap::IndexMap;

pub(in crate::docstring) mod google;
pub(super) mod preformatted;
pub(super) mod rst;
/// Syntax utilities shared by docstring format parsers and renderers.
pub(in crate::docstring) mod syntax;

/// Canonical docstring sections shared by supported formats.
#[derive(Debug, Clone, Copy, PartialEq, Eq, strum_macros::EnumIter)]
pub(in crate::docstring) enum SectionKind {
    /// Function or method parameters.
    Parameters,
    /// Keyword arguments documented separately from the main parameter section.
    KeywordArguments,
    /// Less commonly used parameters listed separately from the main parameter section.
    OtherParameters,
    /// Class or module attributes.
    Attributes,
    /// A returned value.
    Returns,
    /// A yielded value.
    Yields,
    /// Exceptions raised by a callable.
    Raises,
}

impl SectionKind {
    /// Returns the canonical display heading for this section.
    pub(super) const fn heading(self) -> &'static str {
        match self {
            SectionKind::Parameters => "Parameters",
            SectionKind::KeywordArguments => "Keyword Arguments",
            SectionKind::OtherParameters => "Other Parameters",
            SectionKind::Attributes => "Attributes",
            SectionKind::Returns => "Returns",
            SectionKind::Yields => "Yields",
            SectionKind::Raises => "Raises",
        }
    }
}

/// Returns docs for all parameters recognized in the given docstring.
pub(super) fn parameter_documentation(
    raw: &str,
    numpy_parameters: IndexMap<String, String>,
) -> IndexMap<String, String> {
    // Parse Google sections from raw text so PEP 257 trimming does not erase item indentation and
    // make capitalized parameter names look like sibling sections. This means that, for example,
    // raw `Note:\n        context\n\n    Args:\n        value: docs` treats `Args` as part of
    // `Note`, while PEP 257 normalization aligns the two headings.
    let mut parameters = google::parameter_documentation(raw);
    parameters.extend(numpy_parameters);
    parameters.extend(rst::parameter_documentation(raw));
    parameters
}
