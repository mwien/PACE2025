use std::env;
use std::path::PathBuf;
use std::process::Command;

fn build_evalmaxsat() {
    let evalmaxsat_dir = PathBuf::from("native/EvalMaxSAT");

    let dst = cmake::Config::new(&evalmaxsat_dir)
        .build_target("EvalMaxSAT")
        .build();
    println!(
        "cargo:rustc-link-search={}/build/lib/EvalMaxSAT",
        dst.display()
    );
    println!(
        "cargo:rustc-link-search={}/build/lib/cadical",
        dst.display()
    ); //MaLib
    println!("cargo:rustc-link-search={}/build/lib/MaLib", dst.display()); //MaLib
    println!("cargo:rustc-link-lib=static=EvalMaxSAT");
    println!("cargo:rustc-link-lib=static=cadical");
    println!("cargo:rustc-link-lib=static=MaLib");
    #[cfg(target_os = "macos")]
    println!("cargo:rustc-link-lib=c++");
    #[cfg(not(target_os = "macos"))]
    println!("cargo:rustc-link-lib=stdc++");
    println!("cargo:rerun-if-changed={}", evalmaxsat_dir.display());

    let bindings = bindgen::Builder::default()
        .headers([format!(
            "{}/lib/EvalMaxSAT/src/Formula.hpp",
            evalmaxsat_dir.display()
        )])
        .allowlist_function("Eval::.*")
        .opaque_type("std::.*")
        .generate()
        .expect("Failed to generate bindings!");

    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("evalmaxsat_bindings.rs"))
        .expect("Couldn't write bindings!");
}

fn build_maxpre() {
    let maxpre_dir = PathBuf::from("native/maxpre");
    let lib_dir = maxpre_dir.join("src/lib");

    // Step 1: Run `make lib`
    let status = Command::new("make")
        .arg("lib") // Run `make lib`
        .current_dir(&maxpre_dir)
        .status()
        .expect("Failed to run `make lib`");

    if !status.success() {
        panic!("Make failed!");
    }

    // Step 2: Generate Rust bindings
    let bindings = bindgen::Builder::default()
        .header("native/maxpre/src/cpreprocessorinterface.h")
        .clang_arg("-Inative/maxpre/src") // Ensure correct include path
        .opaque_type("std::.*")
        .generate()
        .expect("Failed to generate bindings!");

    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("maxpre_bindings.rs"))
        .expect("Couldn't write bindings!");

    // Step 3: Link the compiled C++ library
    println!("cargo:rustc-link-search=native={}", lib_dir.display());
    println!("cargo:rustc-link-lib=static=maxpre"); // If a static library is built (libmaxpre.a)
                                                    // println!("cargo:rustc-link-lib=dylib=maxpre"); // Uncomment if it's a shared library (.so/.dylib)

    // Step 4: Tell Cargo when to rerun build.rs
    println!("cargo:rerun-if-changed=native/maxpre/Makefile");
    println!("cargo:rerun-if-changed=native/maxpre/src/preprocessorinterface.hpp");
}

fn build_mcqd() {
    println!("cargo:rerun-if-changed=native/cliquesolver/mcqd_entry.cpp");
    println!("cargo:rerun-if-changed=native/cliquesolver/mcqd_entry.h");
    cc::Build::new()
        .cpp(true)
        .file("native/cliquesolver/mcqd_entry.cpp")
        .opt_level(3)
        .flag_if_supported("-Wno-reorder")
        .compile("mcqd_entry.a");
}

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    build_evalmaxsat();
    build_maxpre();
    build_mcqd();
}
