# Use the specified lightweight Rust base image
FROM rust:1.95-slim

# Install system dependencies required for building and compiling
RUN apt-get update && apt-get install -y --no-install-recommends \
    build-essential \
    && rm -rf /var/lib/apt/lists/*

# Set the working directory inside the container
WORKDIR /usr/src/wqc-stark-engine

# Copy the entire workspace into the container
COPY . .

# Build the workspace in release mode for production performance
RUN cargo build --release -p wqc-stark-ffi

# Define the default command to output the generated library paths
CMD ["ls", "-la", "target/release/"]
