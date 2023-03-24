use convert_case::Casing;
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
#[cfg(doc)]
use std::ops::BitOr;
use syn::{
    parse::{Parse, ParseStream},
    parse_macro_input, DataEnum, DeriveInput, Fields, Ident,
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

macro_rules! impl_parse {
    ($first_candidate:ident, $($candidate:ident),* $(,)?) => {
        impl Parse for ReprIntIdent {
            fn parse(tokens: ParseStream) -> syn::Result<Self> {
                let ident = tokens.parse::<Ident>()?;
                if ident == stringify!($first_candidate) {
                    return Ok(Self{ident})
                }
                $(
                    if ident == stringify!($candidate) {
                        return Ok(Self{ident})
                    }
                )*
                Err(syn::Error::new_spanned(ident, concat!(
                    "bitbag: ident must be one of [",
                    stringify!($first_candidate),
                    $(
                        ", ",
                        stringify!($candidate),
                    )*
                    "]"
                )))
            }
        }

    };
}

impl_parse!(i8, u8, i16, u16, i32, u32, i64, u64, i128, u128, isize, usize);

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
        impl bitbag::BitBaggable for #user_ident {
            type Repr = #repr;
            fn into_repr(self) -> Self::Repr {
                self as #repr
            }
            const VARIANTS: &'static [(&'static str, Self, Self::Repr)] = &[
                    #(#names_and_values,)*
                ];

        }
    })
}

fn expand_bitor(input: &DeriveInput) -> syn::Result<TokenStream> {
    let user_ident = &input.ident;
    Ok(quote! {
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

fn snake_case_ident(ident: &Ident) -> Ident {
    Ident::new(
        &ident.to_string().to_case(convert_case::Case::Snake),
        ident.span(),
    )
}

/// Derives a new BoolBag struct for a field-less enum
#[proc_macro_derive(BoolBag)]
pub fn derive_boolbag(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let user_struct = parse_macro_input!(input as DeriveInput);
    if let syn::Data::Enum(user_enum) = user_struct.data {
        let vis = user_struct.vis;
        let user_ident = &user_struct.ident;
        let boolbag_ident = Ident::new(
            &format!("{}BoolBag", user_ident),
            Ident::span(&user_struct.ident),
        );

        let boolbag_fields = user_enum
            .variants
            .iter()
            .map(|variant| snake_case_ident(&variant.ident));

        let set_boolbag_fields_from_bitbag = user_enum.variants.iter().map(|variant| {
            let variant_name = &variant.ident;
            let field_name = snake_case_ident(&variant.ident);
            quote! {
                #field_name: bitbag.is_set(#user_ident::#variant_name)
            }
        });

        let set_bitbag_flags_from_boolbag = user_enum.variants.iter().map(|variant| {
            let variant_name = &variant.ident;
            let field_name = snake_case_ident(&variant.ident);
            quote! {
                if boolbag.#field_name {
                    bitbag.set(#user_ident::#variant_name);
                }
            }
        });

        let appended = quote! {
            #[derive(Debug, Default, Clone, Copy, Eq, PartialEq)]
            #vis struct #boolbag_ident {
                #(pub #boolbag_fields: bool),*
            }

            impl From<bitbag::BitBag<#user_ident>> for #boolbag_ident {
                fn from(bitbag: bitbag::BitBag<#user_ident>) -> #boolbag_ident {
                    #boolbag_ident {
                        #(#set_boolbag_fields_from_bitbag),*
                    }
                }
            }

            impl From<#boolbag_ident> for bitbag::BitBag<#user_ident> {
                fn from(boolbag: #boolbag_ident) -> bitbag::BitBag<#user_ident> {
                    let mut bitbag = bitbag::BitBag::<#user_ident>::default();
                    #(#set_bitbag_flags_from_boolbag);*
                    bitbag
                }
            }
        };

        appended.into()
    } else {
        todo!()
    }
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
