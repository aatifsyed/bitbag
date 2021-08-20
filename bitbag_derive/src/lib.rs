use convert_case::Casing;
use log::{debug, trace};
use pretty_env_logger;
use proc_macro::TokenStream;
use proc_macro_error::{abort, proc_macro_error};
use quote::quote;
#[cfg(doc)]
use std::ops::BitOr;
use syn::{parse_macro_input, DeriveInput, Ident, Meta, NestedMeta};

/// Derives BitBaggable and [`BitOr`] for a field-less enum.
#[proc_macro_error]
#[proc_macro_derive(BitBaggable)]
pub fn derive_bitbaggable(input: TokenStream) -> TokenStream {
    pretty_env_logger::try_init().ok();
    let user_struct = parse_macro_input!(input as DeriveInput);
    debug!("{:#?}", user_struct);

    if let syn::Data::Enum(ref _user_enum) = user_struct.data {
        // Pull out the `u8` in `#[repr(u8)]`
        if let Some(repr) = user_struct.attrs.iter().find_map(|attribute| {
            trace!("inspecting attribute: {:?}", attribute);

            attribute
                .path
                .segments
                .iter()
                .find(|path_segment| path_segment.ident == "repr")?;
            trace!("repr attribute");

            // Try and parse it
            if let Ok(Meta::List(meta_list)) = attribute.parse_meta() {
                trace!("{:#?}", meta_list);
                if meta_list.nested.len() != 1 {
                    abort!(attribute, "#[repr(..)] expected to have a single argument")
                }
                if let NestedMeta::Meta(Meta::Path(argument)) = meta_list.nested.first().unwrap() {
                    Some(argument.segments.first().unwrap().ident.clone())
                } else {
                    abort!(
                        attribute,
                        "#[repr(..)] argument expected to be a single path"
                    )
                }
            } else {
                abort!(
                    attribute,
                    "#[repr(..)] wasn't parseable as a meta attribute"
                )
            }
        }) {
            debug!("Repr is {:#?}", repr);
            let user_ident = user_struct.ident;
            let appended = quote! {
                impl std::convert::Into<#repr> for #user_ident {
                    fn into(self) -> #repr {
                        self as #repr
                    }
                }

                impl std::convert::Into<bitbag::BitBag<#user_ident>> for #user_ident {
                    fn into(self) -> bitbag::BitBag<#user_ident> {
                        bitbag::BitBag::<#user_ident>::new_unchecked(self.into())
                    }
                }

                impl bitbag::BitBaggable for #user_ident {
                    type Repr = #repr;
                }

                impl std::ops::BitOr for #user_ident {
                    type Output = bitbag::BitBag<#user_ident>;

                    fn bitor(self, rhs: Self) -> Self::Output {
                        let mut bag = <Self::Output as Default>::default();
                        bag.set(self);
                        bag.set(rhs);
                        bag
                    }
                }
            };
            debug!("{:#?}", appended);
            appended.into()
        } else {
            abort!(user_struct, "Must have a #[repr(..)] attribute")
        }
    } else {
        abort!(user_struct, "Must be an enum")
    }
}

fn snake_case_ident(ident: &Ident) -> Ident {
    Ident::new(
        &ident.to_string().to_case(convert_case::Case::Snake),
        ident.span(),
    )
}

/// Derives a new BoolBag struct for a field-less enum
#[proc_macro_error]
#[proc_macro_derive(BoolBag)]
pub fn derive_boolbag(input: TokenStream) -> TokenStream {
    pretty_env_logger::try_init().ok();
    let user_struct = parse_macro_input!(input as DeriveInput);
    debug!("{:#?}", user_struct);
    if let syn::Data::Enum(user_enum) = user_struct.data {
        let vis = user_struct.vis;
        let user_ident = &user_struct.ident;
        let boolbag_ident = Ident::new(
            &format!("{}BoolBag", user_ident),
            Ident::span(&user_struct.ident),
        );

        let boolbag_fields = user_enum.variants.iter().map(|variant| {
            trace!("{:#?}", variant);
            snake_case_ident(&variant.ident)
        });

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

        debug!("{:#?}", appended);
        appended.into()
    } else {
        abort!(user_struct, "Must be an enum")
    }
}
