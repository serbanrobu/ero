use std::net::SocketAddr;

use axum::{routing::get, Router};
use clap::Parser;
use color_eyre::Result;
use ero::Entity;
use sqlx::SqlitePool;

#[derive(Parser)]
struct Cli {
    #[arg(short, long, default_value_t = 3000)]
    port: u16,
}

#[tokio::main]
async fn main() -> Result<()> {
    let cli = Cli::parse();
    let app = Router::new().route("/", get(|| async { "[1, 2, 3, 4, 5]" }));
    let addr = SocketAddr::from(([0; 4], cli.port));
    let pool = SqlitePool::connect("sqlite::memory:").await?;

    sqlx::migrate!().run(&pool).await?;

    sqlx::query!(
        "INSERT INTO entities VALUES ($1, $2, $3)",
        "t",
        "\"Bool\"",
        "\"True\""
    )
    .execute(&pool)
    .await?;

    let entity = sqlx::query_as!(
        Entity,
        r#"SELECT name, type AS "type: _", value AS "value: _" FROM entities"#
    )
    .fetch_one(&pool)
    .await?;

    dbg!(entity.value.0);

    axum::Server::bind(&addr).serve(app.into_make_service());

    Ok(())
}
