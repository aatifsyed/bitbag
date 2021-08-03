use log::{debug, trace};
use pretty_env_logger;
use proc_macro::TokenStream;
use proc_macro_error::{abort, proc_macro_error};
use quote::quote;
#[cfg(doc)]
use std::ops::BitOr;
use syn::{parse_macro_input, DeriveInput, Meta, NestedMeta};

/// Derives BitBaggable and [`BitOr`] for a field-less enum.
#[proc_macro_error]
#[proc_macro_derive(BitBaggable)]
pub fn derive(input: TokenStream) -> TokenStream {
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
            if let Meta::List(meta_list) = attribute
                .parse_meta()
                .expect("#[repr(..)] wasn't parseable as a meta attribute")
            {
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
                abort!(attribute, "#[repr] attribute expected to be list-like")
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
