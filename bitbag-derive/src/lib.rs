use proc_macro2::{Span, TokenStream};
use quote::{quote, ToTokens};
use syn::{
    meta::ParseNestedMeta,
    parse::{Parse, ParseStream, Parser},
    parse_macro_input, DataEnum, DeriveInput, Fields, Ident, LitStr,
};

#[derive(Debug, Clone)]
struct ReprIntIdent {
    ident: Ident,
}

impl ToTokens for ReprIntIdent {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.ident.to_tokens(tokens)
    }
}

impl Parse for ReprIntIdent {
    fn parse(tokens: ParseStream) -> syn::Result<Self> {
        let ident = tokens.parse::<Ident>()?;

        macro_rules! impl_parse {
            ($first_candidate:ident, $($candidate:ident),* $(,)?) => {
                if ident == stringify!($first_candidate) {
                    return Ok(Self{ident})
                }
                $(
                    if ident == stringify!($candidate) {
                        return Ok(Self{ident})
                    }
                )*
                return Err(syn::Error::new_spanned(ident, concat!(
                    "bitbag: ident must be one of [",
                    stringify!($first_candidate),
                    $(
                        ", ",
                        stringify!($candidate),
                    )*
                    "]"
                )))

            };
        }

        impl_parse!(i8, u8, i16, u16, i32, u32, i64, u64, i128, u128, isize, usize);
    }
}

fn get_repr_ident(input: &DeriveInput) -> syn::Result<ReprIntIdent> {
    let mut repr_idents = Vec::new();
    for attr in &input.attrs {
        if attr.path().is_ident("repr") {
            repr_idents.push(attr.parse_args::<ReprIntIdent>()?);
        }
    }
    match repr_idents.len() {
        0 => Err(syn::Error::new_spanned(
            input,
            "bitbag: must have a #[repr(..)] attribute",
        )),
        1 => Ok(repr_idents.remove(0)),
        _ => Err(syn::Error::new_spanned(
            input,
            "bitbag: must have only one #[repr(..)] attribute",
        )),
    }
}

fn extract_enum_and_repr(input: &DeriveInput) -> syn::Result<(&DataEnum, ReprIntIdent)> {
    let syn::Data::Enum(data) = &input.data else {
        return Err(
        syn::Error::new_spanned(input, "bitbag: only enums are supported"));
    };
    let repr = get_repr_ident(input)?;

    let mut error = None;
    for variant in &data.variants {
        if let Fields::Named(_) | Fields::Unnamed(_) = variant.fields {
            error
                .get_or_insert(syn::Error::new_spanned(
                    &data.variants,
                    "bitbag: only field-less enums are supported",
                ))
                .combine(syn::Error::new_spanned(
                    &variant.fields,
                    "bitbag: cannot have fields",
                ));
        };
    }
    match error {
        Some(err) => Err(err),
        None => Ok((data, repr)),
    }
}

fn expand_bitbaggable(input: &DeriveInput) -> syn::Result<TokenStream> {
    let (data, repr) = extract_enum_and_repr(input)?;
    let user_ident = &input.ident;
    let names_and_values = data.variants.iter().map(|variant| {
        let ident = &variant.ident;
        let name = syn::LitStr::new(&ident.to_string(), ident.span());
        quote! {
            (#name, Self::#ident, Self::#ident as _)
        }
    });

    Ok(quote! {
        #[automatically_derived]
        impl bitbag::BitBaggable for #user_ident {
            type ReprT = #repr;
            fn into_repr(self) -> Self::ReprT {
                self as #repr
            }
            const VARIANTS: &'static [(&'static str, Self, Self::ReprT)] = &[
                    #(#names_and_values,)*
                ];

        }
    })
}

fn expand_bitor(input: &DeriveInput) -> syn::Result<TokenStream> {
    let user_ident = &input.ident;
    Ok(quote! {
        #[automatically_derived]
        impl core::ops::BitOr<Self> for #user_ident
        where
            Self: bitbag::BitBaggable,
        {
            type Output = bitbag::BitBag<Self>;
            fn bitor(self, rhs: Self) -> Self::Output {
                *bitbag::BitBag::empty()
                    .set(self)
                    .set(rhs)
            }
        }

        #[automatically_derived]
        impl core::ops::BitOr<bitbag::BitBag<Self>> for #user_ident
        where
            Self: bitbag::BitBaggable,
        {
            type Output = bitbag::BitBag<Self>;
            fn bitor(self, mut rhs: bitbag::BitBag<Self>) -> Self::Output {
                *rhs.set(self)
            }
        }
    })
}

#[proc_macro_derive(BitBaggable)]
pub fn derive_bitbaggable(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let user_struct = parse_macro_input!(input as DeriveInput);
    expand_bitbaggable(&user_struct)
        .unwrap_or_else(syn::Error::into_compile_error)
        .into()
}

#[proc_macro_derive(BitOr)]
pub fn derive_bitor(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let user_struct = parse_macro_input!(input as DeriveInput);
    expand_bitor(&user_struct)
        .unwrap_or_else(syn::Error::into_compile_error)
        .into()
}

#[derive(Debug)]
struct CheckConfig {
    unit_test: bool,
    compile_test: bool,
}

impl Parse for CheckConfig {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut config = CheckConfig {
            unit_test: false,
            compile_test: false,
        };

        syn::meta::parser(|stage| config.parse_stage(stage)).parse2(input.parse()?)?;
        if !config.unit_test && !config.compile_test {
            config.unit_test = true; // default behaviour if left unspecified
        }
        Ok(config)
    }
}

impl CheckConfig {
    fn parse_stage(&mut self, stage: ParseNestedMeta) -> syn::Result<()> {
        if stage.path.is_ident("unit_test") || stage.path.is_ident("unit") {
            if !stage.input.is_empty() {
                return Err(stage.error("`unit_test` doesn't take any arguments"));
            }
            if self.unit_test {
                return Err(stage.error("`unit_test` can only be specified once"));
            }
            self.unit_test = true
        } else if stage.path.is_ident("compile_test") || stage.path.is_ident("compile") {
            if !stage.input.is_empty() {
                return Err(stage.error("`compile_test` doesn't take any arguments"));
            }
            if self.compile_test {
                return Err(stage.error("`compile_test` can only be specified once"));
            }
            self.compile_test = true
        } else {
            return Err(stage.error(format!(
                "unexpected argument `{}`, expected `unit_test` or `compile_test``",
                stage.path.to_token_stream()
            )));
        }
        Ok(())
    }
}

fn expand_check_nonoverlapping(
    config: &CheckConfig,
    input: &DeriveInput,
) -> syn::Result<TokenStream> {
    let (data, repr) = extract_enum_and_repr(input)?;

    let unit_test = match config.unit_test {
        true => {
            let struct_ident = &input.ident;
            let fn_ident = Ident::new(
                &format!("bitbag_unit_test_{}", &input.ident),
                input.ident.span(),
            );
            Some(quote!(
                #[cfg(test)]
                #[test]
                #[allow(non_snake_case)]
                fn #fn_ident() {
                    bitbag::check_nonoverlapping::<#struct_ident>().unwrap();
                }
            ))
        }
        false => None,
    };
    let compile_test = match config.compile_test {
        true => {
            let mut pairs = Vec::new();
            for right_ix in (0..data.variants.len()).rev() {
                for left_ix in 0..right_ix {
                    pairs.push((
                        &data.variants[left_ix].ident,
                        &data.variants[right_ix].ident,
                    ))
                }
            }
            let checkers = pairs.into_iter().map(|(left, right)| {
                let struct_ident = &input.ident;
                let panic_msg = LitStr::new(
                    &format!("{left} and {right} have overlapping bits"),
                    Span::call_site(),
                );
                quote!(
                    {
                        let left = #struct_ident::#left as #repr;
                        let right = #struct_ident::#right as #repr;
                        if left & right != 0 {
                            panic!(#panic_msg)
                        }
                    }
                )
            });
            Some(quote!(
                #[allow(warnings)]
                const _: () = {
                    #(#checkers)*
                };
            ))
        }
        false => None,
    };
    Ok(quote!(
        #input
        #unit_test
        #compile_test
    ))
}

#[proc_macro_attribute]
pub fn check_nonoverlapping(
    attr: proc_macro::TokenStream,
    item: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let input = parse_macro_input!(item as DeriveInput);
    let config = parse_macro_input!(attr as CheckConfig);
    expand_check_nonoverlapping(&config, &input)
        .unwrap_or_else(syn::Error::into_compile_error)
        .into()
}

#[cfg(test)]
mod tests {
    #[test]
    fn trybuild() {
        let t = trybuild::TestCases::new();
        t.pass("trybuild/pass/**/*.rs");
        t.compile_fail("trybuild/fail/**/*.rs")
    }
}
