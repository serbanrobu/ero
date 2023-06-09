CREATE TABLE context (
    name TEXT NOT NULL PRIMARY KEY,
    type JSON NOT NULL,
    value JSON NOT NULL,
    mutable BOOLEAN NOT NULL
);
