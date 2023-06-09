use std::{collections::HashSet, env};

// use axum::{routing::get, Router};
// use clap::Parser;
use color_eyre::Result;
use ero::{Command, Ctx, Env, Type, Value, Var};
use rustyline::{config::Configurer, error::ReadlineError, EditMode, Editor};
use sqlx::{types::Json, PgPool};

// #[derive(Parser)]
// struct Cli {
//     #[arg(short, long, default_value_t = 3000)]
//     port: u16,
// }

#[tokio::main]
async fn main() -> Result<()> {
    let db_url = env::var("DATABASE_URL")?;
    // let cli = Cli::parse();
    let pool = PgPool::connect(&db_url).await?;

    sqlx::migrate!().run(&pool).await?;

    // let _entity = sqlx::query_as!(
    //     Entity,
    //     r#"SELECT name, type AS "type: _", value AS "value: _" FROM entities"#
    // )
    // .fetch_one(&pool)
    // .await?;

    // let app = Router::new().route("/", get(|| async { "[1, 2, 3, 4, 5]" }));
    // let addr = SocketAddr::from(([0; 4], cli.port));
    // axum::Server::bind(&addr).serve(app.into_make_service());

    let mut rl = Editor::<()>::new()?;
    rl.set_edit_mode(EditMode::Vi);

    loop {
        match rl.readline(">>> ") {
            Ok(line) => {
                rl.add_history_entry(&line);

                let result: Result<_> = async {
                    let cmd: Command = line.parse()?;

                    match cmd {
                        Command::Eval(e) => {
                            let mut xs = HashSet::new();
                            e.free_vars(&mut xs);

                            let vars = sqlx::query!(
                                r#"
                                SELECT name, type AS "type: Json<Type>", value AS "value: Json<Value>"
                                FROM context
                                WHERE name = ANY($1::TEXT[])
                                "#,
                                &xs.iter().cloned().collect::<Vec<_>>(),
                            )
                            .fetch_all(&pool)
                            .await?;

                            let mut ctx = Ctx::new();
                            let mut env = Env::new();

                            for var in vars {
                                ctx.insert(var.name.clone(), var.r#type.0);
                                env.insert(var.name, var.value.0);
                            }

                            let ty = e.synth(&ctx, &env)?;
                            let val = e.eval(&env);

                            println!("{} : {}", val.quote(&xs), ty.quote(&xs));

                            Ok(true)
                        }
                        Command::Let(mutable, x, e) => {
                            let mut xs = HashSet::new();
                            e.free_vars(&mut xs);

                            let vars = sqlx::query_as!(
                                Var,
                                r#"
                                SELECT name, type AS "type: _", value AS "value: _", mutable
                                FROM context
                                WHERE name = ANY($1::TEXT[])
                                "#,
                                &xs.iter().cloned().collect::<Vec<_>>(),
                            )
                            .fetch_all(&pool)
                            .await?;

                            let mut ctx = Ctx::new();
                            let mut env = Env::new();

                            if mutable {
                                for var in vars {
                                    ctx.insert(var.name.clone(), var.r#type.0);

                                    if !var.mutable {
                                        env.insert(var.name, var.value.0);
                                    }
                                }
                            } else {
                                for var in vars {
                                    ctx.insert(var.name.clone(), var.r#type.0);
                                    env.insert(var.name, var.value.0);
                                }
                            }

                            let t = e.synth(&ctx, &env)?;
                            let v = e.eval(&env);

                            let var = Var {
                                name: x,
                                r#type: Json(t),
                                value: Json(v),
                                mutable,
                            };

                            sqlx::query!(
                                r#"
                                INSERT INTO context VALUES ($1, $2, $3, $4)
                                ON CONFLICT (name) DO UPDATE SET type = $2, value = $3, mutable = $4
                                "#,
                                var.name,
                                var.r#type as _,
                                var.value as _,
                                var.mutable,
                            )
                            .execute(&pool)
                            .await?;

                            Ok(true)
                        }
                        Command::List => {
                            let vars = sqlx::query!(
                                r#"SELECT name, type AS "type: Json<Type>", value AS "value: Json<Value>" FROM context"#
                            )
                            .fetch_all(&pool)
                            .await?;

                            let mut ctx = Ctx::new();
                            let mut env = Env::new();

                            for var in vars {
                                ctx.insert(var.name.clone(), var.r#type.0);
                                env.insert(var.name, var.value.0);
                            }

                            let xs = ctx.keys().cloned().collect();

                            for (x, t) in ctx {
                                println!(
                                    "{x} : {} := {}",
                                    t.quote(&xs),
                                    env.get(&x).unwrap().quote(&xs)
                                );
                            }

                            Ok(true)
                        }
                        Command::Quit => {
                            println!("Bye bye!");
                            Ok(false)
                        }
                    }
                }
                .await;

                match result {
                    Ok(true) => continue,
                    Ok(false) => break,
                    Err(err) => eprintln!("{err}"),
                }
            }
            Err(ReadlineError::Interrupted) => {
                println!("CTRL-C");
                break;
            }
            Err(ReadlineError::Eof) => {
                println!("CTRL-D");
                break;
            }
            Err(err) => {
                eprintln!("Error: {err}");
                break;
            }
        }
    }

    Ok(())
}
