use log::{debug, trace};
use pretty_env_logger;
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput, Meta, NestedMeta};

#[proc_macro_derive(BitBaggable)]
pub fn derive(input: TokenStream) -> TokenStream {
    pretty_env_logger::init();
    let user_struct = parse_macro_input!(input as DeriveInput);
    debug!("{:#?}", user_struct);

    if let syn::Data::Enum(_user_enum) = user_struct.data {
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
                assert!(
                    meta_list.nested.len() == 1,
                    "#[repr(..)] expected to have a single argument"
                );
                if let NestedMeta::Meta(Meta::Path(argument)) = meta_list.nested.first().unwrap() {
                    Some(argument.segments.first().unwrap().ident.clone())
                } else {
                    panic!("#[repr(..)] argument expected to be a single path")
                }
            } else {
                panic!("#[repr] attribute expected to be list-like")
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
            };
            debug!("{:#?}", appended);
            appended.into()
        } else {
            panic!("Must have a #[repr(..)] attribute")
        }
    } else {
        panic!("Must be an enum")
    }
}
