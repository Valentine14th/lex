from models import Base, ENGINE, Session, Person

# --- Setup the database ---
Base.metadata.create_all(ENGINE) # Create all tables defined in gdprfs/models.py
print("[DB] gdprfs.db's tables (empty) initialized successfully.")

session = Session() # open a session to create initial data

if not session.query(Person).count():  # only initialize once
    potential_users = [
        {"first_name": "Alice", "last_name": "A"},
        {"first_name": "Bob", "last_name": "B"},
        {"first_name": "Charlie", "last_name": "C"},
        {"first_name": "Dave", "last_name": "D"},
        {"first_name": "Eve", "last_name": "E"}
    ]

    for user in potential_users:
        p = Person(
            uid=None,               # they haven’t registered yet
            first_name=user["first_name"],
            last_name=user["last_name"],
            registered=False,       # mark them as potential users
        )
        session.add(p)

    session.commit()
    print(f"[DB] Added {len(potential_users)} potential users.")
else:
    print("[DB] Database already initialized")

session.close()